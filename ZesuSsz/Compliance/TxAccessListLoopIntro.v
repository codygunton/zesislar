Require Import ZesuSsz.Automation2.ByteArrays.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Automation2.VmClosed.
Require Export ZesuSsz.Compliance.TxAccessListWordHints.
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

(* A closed stored word whose little-endian bytes are the closed literal
   `bytes`, decided on the byte values. *)
Class TxClosedWordBytes (w : bv 64) (bytes : list byte) : Prop :=
  tx_closed_word_bytes : bytes = bv_to_little_endian 8 8 (bv_unsigned w).

Lemma tx_closed_word_bytes_intro (w : bv 64) (bytes : list byte) :
  map bv_unsigned bytes = map bv_unsigned (bv_to_little_endian 8 8 (bv_unsigned w)) ->
  TxClosedWordBytes w bytes.
Proof. apply tx_byte_list_eq. Qed.

Global Hint Extern 0 (TxClosedWordBytes ?w ?bytes) =>
  (ZesuSsz.Automation2.VmClosed.zesu_closed_term w;
   ZesuSsz.Automation2.VmClosed.zesu_closed_term bytes;
   apply tx_closed_word_bytes_intro; vm_compute; reflexivity) : typeclass_instances.

(* An empty header the block stored as three words (pointer p, length 0,
   capacity 0; the +0x170 exit to the +0x248 join): the pointer word's value. *)
Class TxEmptyListWord (w : bv 64) (p : Z) : Prop :=
  tx_empty_list_word : bv_unsigned w = p.

Global Hint Extern 0 (TxEmptyListWord ?w ?p) =>
  (is_evar p; ZesuSsz.Automation2.VmClosed.zesu_closed_term w;
   let v := eval vm_compute in (bv_unsigned w) in
   unify p v; vm_compute; reflexivity) : typeclass_instances.

Lemma tx_header_word_bytes (v : Z) : word64Bytes v = bv_to_little_endian 8 8 v.
Proof. rewrite zesu_word64_bytes_encoding. unfold word64Bytes. reflexivity. Qed.

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

  Lemma tx_header_words_array (a : Z) (w0 w1 w2 : bv 64) :
    a ↦ₘ w0 -∗ (a + 8) ↦ₘ w1 -∗ (a + 16) ↦ₘ w2 -∗
    a ↦ₘ∗ (word64Bytes (bv_unsigned w0) ++ word64Bytes (bv_unsigned w1) ++
           word64Bytes (bv_unsigned w2)).
  Proof.
    iIntros "H0 H1 H2". rewrite !tx_header_word_bytes app_assoc.
    iDestruct (mem_mapsto_u64_pair_to_byte_array with "H0 H1") as "H01".
    iDestruct (mem_mapsto_mapsto_to_byte_array with "H2") as "H2".
    iApply (mem_mapsto_array_app_combine_at 8%N a (DfracOwn 1) _ _ 16 with "H01").
    { rewrite length_app !length_bv_to_little_endian; lia. }
    rewrite /= Z.mul_1_l. iExact "H2".
  Qed.

  (* The same header stored as three words: the length and capacity words
     are taken from the context next to the pointer word. *)
  Lemma subsume_tx_empty_list_header_words A (a1 a2 : Z) (w : bv 64) (p eb la : Z)
      `{!TxEmptyListWord w p} `{!TxEmptyList p eb la}
      (state : A -> ArrayListState) G :
    (⌜a1 = a2⌝ ∗ (a1 + 8) ↦ₘ (BV 64 0) ∗ (a1 + 16) ↦ₘ (BV 64 0) ∗ ⌜0 <= p <= 2 ^ 64⌝ ∗
      (arrayListBuffer eb la (arrayListEmpty p) -∗
        ∃ x, ⌜state x = arrayListEmpty p⌝ ∗ G x))%I ⊢
    subsume (a1 ↦ₘ w) (fun x => a2 ↦ₘ∗ arrayListHeaderBytes (state x)) G.
  Proof.
    iIntros "(-> & H1 & H2 & %Hp & HG) H0".
    iDestruct ("HG" with "[]") as (x Hstate) "HG"; [by iApply tx_empty_buffer|].
    iExists x. iFrame "HG". rewrite Hstate /arrayListHeaderBytes /arrayListEmpty.
    cbn [arrayListPointer arrayListLength arrayListCapacity].
    rewrite -(tx_empty_list_word (w:=w) (p:=p)).
    iApply (tx_header_words_array with "H0 H1 H2").
  Qed.
  Definition subsume_tx_empty_list_header_words_inst :=
    [instance subsume_tx_empty_list_header_words].
  Global Existing Instance subsume_tx_empty_list_header_words_inst | 0.

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

  (* A closed stored word read as the closed bytes of its little-endian
     image (the frame word at +80 the code stores before the loop). *)
  Lemma subsume_tx_word_bytes A (a1 a2 : Z) (w : bv 64) (bytes : list byte)
      `{!TxClosedWordBytes w bytes} G :
    (⌜a1 = a2⌝ ∗ ∃ x, G x)%I ⊢
    subsume (a1 ↦ₘ w) (fun _ : A => a2 ↦ₘ∗ bytes) G.
  Proof.
    rewrite (@tx_closed_word_bytes w bytes _).
    iIntros "[-> [%x HG]] Hw". iExists x. iFrame "HG".
    iApply (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_mapsto_to_byte_array with "Hw").
  Qed.
  Definition subsume_tx_word_bytes_inst := [instance subsume_tx_word_bytes].
  Global Existing Instance subsume_tx_word_bytes_inst | 96.
End tx_loop_intro.
