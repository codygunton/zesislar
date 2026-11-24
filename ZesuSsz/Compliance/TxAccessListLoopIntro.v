Require Import ZesuSsz.Automation2.ByteArrays.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Automation2.VmClosed.
Import ListNotations.
Local Open Scope Z_scope.

(* The owned state of txAccessList's two loops at their entries (+0xc4 from
   +0xac, +0x18c from +0x188): the lists the code has just initialised are
   empty, and the keys slices of the finished entries are none.

   - A list header the block stored as literal bytes (pointer p, length 0,
     capacity 0) is the header of `arrayListEmpty p`; its buffer (the empty
     array at p, a zero-byte region, a zero-byte allocator token) owns
     nothing and is handed over with it. The empty pointer is the list's
     alignment, so it names the element type: 8 the entries, 1 the keys
     (ArrayListContract.v).
   - The keys slices of no finished entry are `txAccessListKeysSlices [] []`;
     when the entry holds keys slices (a back edge, the inner loop's entry)
     they are the held ones. *)

(* The literal header bytes of the empty list at `p`, decided on the byte
   values (closed terms only). *)
Class TxEmptyListHeader (bytes : list byte) (p : Z) : Prop :=
  tx_empty_list_header : bytes = arrayListHeaderBytes (arrayListEmpty p).

Lemma tx_byte_list_eq (l1 l2 : list byte) :
  map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate; [done|].
  injection H as Hab Hl. f_equal; [by apply bv_eq | by apply IH].
Qed.

Lemma tx_empty_list_header_intro (bytes : list byte) (p : Z) :
  map bv_unsigned bytes = map bv_unsigned (arrayListHeaderBytes (arrayListEmpty p)) ->
  TxEmptyListHeader bytes p.
Proof. apply tx_byte_list_eq. Qed.

Ltac tx_empty_list_header :=
  lazymatch goal with
  | |- TxEmptyListHeader ?bytes ?p =>
      is_evar p;
      ZesuSsz.Automation2.VmClosed.zesu_closed_term bytes;
      let n := eval vm_compute in (length bytes) in
      lazymatch n with 24%nat => idtac end;
      let v := eval vm_compute in (bv_unsigned (nth 0 bytes (BV 8 0)) +
        256 * bv_unsigned (nth 1 bytes (BV 8 0)) +
        65536 * bv_unsigned (nth 2 bytes (BV 8 0)) +
        16777216 * bv_unsigned (nth 3 bytes (BV 8 0))) in
      apply (tx_empty_list_header_intro bytes v); vm_compute; reflexivity
  end.
Global Hint Extern 0 (TxEmptyListHeader _ _) => tx_empty_list_header : typeclass_instances.

(* The element size and alignment of the empty list at each empty pointer. *)
Class TxEmptyList (p elementBytes log2Align : Z) : Prop := {}.
Global Instance tx_empty_entries_list :
  TxEmptyList entriesEmptyPointer entriesElementBytes entriesLog2Alignment := {}.
Global Instance tx_empty_keys_list :
  TxEmptyList keysEmptyPointer keysElementBytes keysLog2Alignment := {}.
Global Hint Mode TxEmptyList ! - - : typeclass_instances.

Section tx_loop_intro.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma tx_empty_buffer (p elementBytes log2Align : Z) :
    0 <= p <= 2 ^ 64 -> ⊢ arrayListBuffer elementBytes log2Align (arrayListEmpty p).
  Proof.
    intros Hp. rewrite /arrayListBuffer /= altFlBlock_unfold /altFlBlockSlack /=.
    rewrite ?Z.mul_0_l ?Z.sub_0_r ?Z.add_0_r.
    iSplitL; [|iSplitL; [|iSplitL; [|by iPureIntro]]]; try by iApply mem_mapsto_uninit_0.
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
    iExists 1%N. iSplit; [done|]. iSplit; [iPureIntro; cbn; lia|]. done.
  Qed.

  (* A header stored as the literal empty header: the list state is the
     empty list at its pointer, and its empty buffer is handed over. *)
  Lemma subsume_tx_empty_list_header A (a1 a2 : Z) (bytes : list byte) (p eb la : Z)
      `{!TxEmptyListHeader bytes p} `{!TxEmptyList p eb la}
      (state : A -> ArrayListState) G :
    (⌜0 <= p <= 2 ^ 64⌝ ∗ (arrayListBuffer eb la (arrayListEmpty p) -∗
      ∃ x, ⌜a1 = a2⌝ ∗ ⌜state x = arrayListEmpty p⌝ ∗ G x))%I ⊢
    subsume (a1 ↦ₘ∗ bytes) (fun x => a2 ↦ₘ∗ arrayListHeaderBytes (state x)) G.
  Proof.
    iIntros "(%Hp & HG) Hbytes".
    iDestruct ("HG" with "[]") as (x) "(-> & %Hstate & HG)"; [by iApply tx_empty_buffer|].
    iExists x. rewrite Hstate -(tx_empty_list_header (bytes:=bytes)). iFrame.
  Qed.
  Definition subsume_tx_empty_list_header_inst := [instance subsume_tx_empty_list_header].
  Global Existing Instance subsume_tx_empty_list_header_inst | 0.

  (* The keys slices of the finished entries: the held ones. *)
  Global Instance txAccessListKeysSlices_related A
      (done : A -> list AccessListEntryValue) (images : A -> list TxAccessListEntryImage) :
    RelatedTo (fun x => txAccessListKeysSlices (done x) (images x)) := {|
    rt_fic := FindDirect (fun di : list AccessListEntryValue * list TxAccessListEntryImage =>
      txAccessListKeysSlices di.1 di.2) |}.

  Lemma subsume_txAccessListKeysSlices A done0 images0
      (done : A -> list AccessListEntryValue) (images : A -> list TxAccessListEntryImage) G :
    (∃ x, ⌜done x = done0⌝ ∗ ⌜images x = images0⌝ ∗ G x)%I ⊢
    subsume (txAccessListKeysSlices done0 images0)
      (fun x => txAccessListKeysSlices (done x) (images x)) G.
  Proof. iIntros "(%x & <- & <- & HG) Hs". iExists x. iFrame. Qed.
  Definition subsume_txAccessListKeysSlices_inst := [instance subsume_txAccessListKeysSlices].
  Global Existing Instance subsume_txAccessListKeysSlices_inst.

  (* None held (the outer loop's entry): no entry is finished. *)
  Lemma simpl_goal_txAccessListKeysSlices_empty done images T :
    ⌜done = [] /\ images = []⌝ ∗ T ⊢
    simplify_goal (txAccessListKeysSlices done images) T.
  Proof.
    iIntros "[[%Hd %Hi] $]". subst. unfold txAccessListKeysSlices. done.
  Qed.
  Definition simpl_goal_txAccessListKeysSlices_empty_inst :=
    [instance simpl_goal_txAccessListKeysSlices_empty with 50%N].
  Global Existing Instance simpl_goal_txAccessListKeysSlices_empty_inst.

  (* A stored word read as the 8 bytes of its little-endian image (the
     frame word at +80 the code stores before the loop). *)
  Lemma subsume_tx_word_bytes A (a1 a2 : Z) (w : bv 64) (requested : A -> list byte) G
      `{!TCFastDone (forall x : A, length (requested x) = 8%nat)} :
    (∃ x, ⌜a1 = a2⌝ ∗ ⌜requested x = bv_to_little_endian 8 8 (bv_unsigned w)⌝ ∗ G x)%I ⊢
    subsume (a1 ↦ₘ w) (fun x => a2 ↦ₘ∗ requested x) G.
  Proof. exact (subsume_mem_word_byte_array A a1 a2 8 w requested G). Qed.
  Definition subsume_tx_word_bytes_inst := [instance subsume_tx_word_bytes].
  Global Existing Instance subsume_tx_word_bytes_inst | 96.
End tx_loop_intro.
