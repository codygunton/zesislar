(* Bridges between the toOwnedSlice contract (ArrayListContract.v) and the
   generated block entries of its regions, parametrised over the element size,
   the alignment and the empty pointer: keysToOwnedSlice (32, 0, 1) and
   entriesToOwnedSlice (40, 3, 8) instantiate them. Each region's composition
   (<Region>GeneratedComposition.v) uses them in its start and end bridges:
   - the three outcomes of the contract (empty list, out of memory, copied
     slice) and their toOwnedSliceAllows proofs;
   - the zero-size buffers of the empty lists, built from nothing;
   - the buffer of the copied slice from the copy and its allocator token;
   - the stack frame cells as uninitialized bytes and back;
   - the result and header images that the generated return packages spell
     byte by byte. *)
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Import ListNotations.
Open Scope Z_scope.

(* ---- The three outcomes. ---- *)

Definition toOwnedEmptyOutcome (emptyPointer : Z) (args : ToOwnedSliceArgs) :
    ToOwnedSliceOutcome :=
  {| toOwnedKind := arrayListSuccess;
     toOwnedListAfter := arrayListEmpty emptyPointer;
     toOwnedSlice := arrayListEmpty (arrayListPointer (toOwnedList args));
     toOwnedResultAfter := arrayListResultImage (toOwnedResultBefore args)
       (arrayListPointer (toOwnedList args)) 0 |}.

Definition toOwnedOutOfMemoryOutcome (emptyPointer : Z) (args : ToOwnedSliceArgs) :
    ToOwnedSliceOutcome :=
  {| toOwnedKind := arrayListOutOfMemory;
     toOwnedListAfter := toOwnedList args;
     toOwnedSlice := arrayListEmpty emptyPointer;
     toOwnedResultAfter := arrayListErrorImage (toOwnedResultBefore args)
       arrayListOutOfMemoryCode |}.

Definition toOwnedCopiedSlice (args : ToOwnedSliceArgs) (pointer : Z) : ArrayListState :=
  {| arrayListPointer := pointer;
     arrayListLength := arrayListLength (toOwnedList args);
     arrayListCapacity := arrayListLength (toOwnedList args);
     arrayListItems := arrayListItems (toOwnedList args) |}.

Definition toOwnedSuccessOutcome (args : ToOwnedSliceArgs) (pointer : Z) :
    ToOwnedSliceOutcome :=
  {| toOwnedKind := arrayListSuccess;
     toOwnedListAfter := arrayListEmpty (arrayListPointer (toOwnedList args));
     toOwnedSlice := toOwnedCopiedSlice args pointer;
     toOwnedResultAfter := arrayListResultImage (toOwnedResultBefore args)
       pointer (arrayListLength (toOwnedList args)) |}.

Lemma toOwnedEmpty_wellFormed (elementBytes pointer : Z) :
  0 < pointer < 2 ^ 64 -> arrayListWellFormed elementBytes (arrayListEmpty pointer).
Proof. intros. unfold arrayListWellFormed, arrayListEmpty; cbn. split_and!; lia. Qed.

Lemma toOwnedEmpty_allows (elementBytes emptyPointer : Z) (args : ToOwnedSliceArgs) :
  0 < emptyPointer < 2 ^ 64 ->
  toOwnedSliceDomain elementBytes args ->
  arrayListLength (toOwnedList args) = 0 ->
  toOwnedSliceAllows elementBytes emptyPointer args (toOwnedEmptyOutcome emptyPointer args).
Proof.
  intros He Hd Hlen. pose proof (toOwnedSliceDomainRanges _ _ Hd) as (_ & _ & Hp & _).
  unfold toOwnedSliceAllows, toOwnedEmptyOutcome; cbn. rewrite Hlen; cbn.
  split_and!; try reflexivity; apply toOwnedEmpty_wellFormed; lia.
Qed.

Lemma toOwnedOutOfMemory_allows (elementBytes emptyPointer : Z) (args : ToOwnedSliceArgs) :
  0 < emptyPointer < 2 ^ 64 ->
  toOwnedSliceDomain elementBytes args ->
  arrayListLength (toOwnedList args) <> 0 ->
  toOwnedSliceAllows elementBytes emptyPointer args
    (toOwnedOutOfMemoryOutcome emptyPointer args).
Proof.
  intros He Hd Hlen. pose proof Hd as [Hwf _].
  unfold toOwnedSliceAllows, toOwnedOutOfMemoryOutcome; cbn.
  apply Z.eqb_neq in Hlen. rewrite Hlen.
  split_and!; try reflexivity; [exact Hwf|apply toOwnedEmpty_wellFormed; lia].
Qed.

Lemma toOwnedSuccess_allows (elementBytes emptyPointer : Z) (args : ToOwnedSliceArgs)
    (pointer : Z) :
  toOwnedSliceDomain elementBytes args ->
  arrayListLength (toOwnedList args) <> 0 ->
  0 < pointer < 2 ^ 64 ->
  arrayListRamRange pointer (arrayListLength (toOwnedList args) * elementBytes) ->
  toOwnedSliceAllows elementBytes emptyPointer args (toOwnedSuccessOutcome args pointer).
Proof.
  intros Hd Hlen Hp Hram. pose proof (toOwnedSliceDomainRanges _ _ Hd) as (Hl & Hitems & Hold & _).
  unfold toOwnedSliceAllows, toOwnedSuccessOutcome, toOwnedCopiedSlice; cbn.
  apply Z.eqb_neq in Hlen as Hlen'. rewrite Hlen'.
  split_and!; try reflexivity; [apply toOwnedEmpty_wellFormed; lia|].
  unfold arrayListWellFormed; cbn. split_and!; try lia; intros _; exact Hram.
Qed.

Lemma toOwnedEmpty_scratch (elementBytes emptyPointer : Z) (args : ToOwnedSliceArgs) :
  arrayListLength (toOwnedList args) = 0 ->
  toOwnedSliceScratchAfter elementBytes args (toOwnedEmptyOutcome emptyPointer args) =
    toOwnedScratchBefore args.
Proof. intros Hlen. unfold toOwnedSliceScratchAfter. by rewrite Hlen. Qed.

Lemma toOwnedOutOfMemory_scratch (elementBytes emptyPointer : Z) (args : ToOwnedSliceArgs) :
  toOwnedSliceScratchAfter elementBytes args (toOwnedOutOfMemoryOutcome emptyPointer args) =
    toOwnedScratchBefore args.
Proof. unfold toOwnedSliceScratchAfter. by destruct (_ =? 0). Qed.

Lemma toOwnedSuccess_scratch (elementBytes : Z) (args : ToOwnedSliceArgs) (pointer : Z) :
  arrayListLength (toOwnedList args) <> 0 ->
  toOwnedSliceScratchAfter elementBytes args (toOwnedSuccessOutcome args pointer) =
    word64Bytes (arrayListLength (toOwnedList args) * elementBytes).
Proof.
  intros Hlen. unfold toOwnedSliceScratchAfter. apply Z.eqb_neq in Hlen. by rewrite Hlen.
Qed.

(* ---- Byte images. ---- *)

(* The result image of a success, as the return packages spell it. *)
Lemma toOwned_result_image (before : list byte) (pointer length : Z) :
  take 0 before ++ (bv_to_little_endian (Z.of_nat 8) 8 pointer ++
    (bv_to_little_endian (Z.of_nat 8) 8 length ++
     (bv_to_little_endian (Z.of_nat 2) 8 (bv_unsigned (BV 16 0)) ++ drop (16 + 2) before))) =
  arrayListResultImage before pointer length.
Proof.
  unfold arrayListResultImage. rewrite !arrayList_word64Bytes_le. reflexivity.
Qed.

(* The error image of out of memory (code 2). *)
Lemma toOwned_error_image (before : list byte) :
  take 16 before ++ (bv_to_little_endian (Z.of_nat 2) 8 (bv_unsigned (BV 16 2)) ++
    drop (16 + 2) before) =
  arrayListErrorImage before arrayListOutOfMemoryCode.
Proof. reflexivity. Qed.

(* The header of a list reset to the empty list at a new pointer. *)
Lemma toOwned_header_reset (state : ArrayListState) (pointer : Z) :
  take 0 (arrayListHeaderBytes state) ++ (bv_to_little_endian (Z.of_nat 8) 8 pointer ++
    (bv_to_little_endian (Z.of_nat 8) 8 (bv_unsigned (BV 64 0)) ++
     (bv_to_little_endian (Z.of_nat 8) 8 (bv_unsigned (BV 64 0)) ++
      drop (16 + 8) (arrayListHeaderBytes state)))) =
  arrayListHeaderBytes (arrayListEmpty pointer).
Proof.
  unfold arrayListHeaderBytes, arrayListEmpty. cbn [arrayListPointer arrayListLength arrayListCapacity].
  rewrite !arrayList_word64Bytes_le. reflexivity.
Qed.

(* The header of a list whose length and capacity are cleared (the pointer stays). *)
Lemma toOwned_header_clear (state : ArrayListState) :
  take 8 (arrayListHeaderBytes state) ++
    (bv_to_little_endian (Z.of_nat 8) 8 (bv_unsigned (BV 64 0)) ++
     (bv_to_little_endian (Z.of_nat 8) 8 (bv_unsigned (BV 64 0)) ++
      drop (16 + 8) (arrayListHeaderBytes state))) =
  arrayListHeaderBytes (arrayListEmpty (arrayListPointer state)).
Proof.
  unfold arrayListHeaderBytes, arrayListEmpty. cbn [arrayListPointer arrayListLength arrayListCapacity].
  rewrite !arrayList_word64Bytes_le. reflexivity.
Qed.

(* ---- Stack frame cells. ---- *)

Lemma toOwned_frame_address (sp c d : bv 64) (frame : Z) :
  frame <= bv_unsigned sp -> bv_unsigned c = 2 ^ 64 - frame -> bv_unsigned d < frame ->
  bv_unsigned (bv_add (bv_add sp c) d) = bv_unsigned sp - frame + bv_unsigned d.
Proof.
  intros Hsp Hc Hd. pose proof (bv_unsigned_in_range _ sp) as Hs.
  pose proof (bv_unsigned_in_range _ d) as Hdr. unfold bv_modulus in Hs, Hdr.
  rewrite !bv_add_unsigned Hc. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
  rewrite Zplus_mod_idemp_l.
  replace (bv_unsigned sp + (2 ^ 64 - frame) + bv_unsigned d)
    with ((bv_unsigned sp - frame + bv_unsigned d) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section spatial.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma toOwned_bytes_nil (a : Z) :
    0 <= a <= 2 ^ 64 -> ⊢ a ↦ₘ∗ ([] : list byte).
  Proof.
    intros Ha. rewrite mem_mapsto_array_eq. iExists 1%N. cbn.
    iSplit; [done|]. iSplit; [iPureIntro; lia|]. done.
  Qed.

  Lemma toOwned_empty_buffer (elementBytes log2Align pointer : Z) :
    0 <= pointer < 2 ^ 64 ->
    ⊢ arrayListBuffer elementBytes log2Align (arrayListEmpty pointer).
  Proof.
    intros Hp. rewrite /arrayListBuffer /arrayListEmpty altFlBlock_unfold /=.
    replace (pointer + 0 * elementBytes) with pointer by lia.
    replace ((0 - 0) * elementBytes) with 0 by lia.
    replace (0 * elementBytes) with 0 by lia.
    replace (pointer + 0) with pointer by lia.
    rewrite /altFlBlockSlack /= !mem_mapsto_uninit_0.
    iSplit; [by iApply toOwned_bytes_nil; lia|].
    iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; lia|]. iPureIntro. done.
  Qed.

  Lemma toOwned_copied_buffer (elementBytes log2Align : Z) (args : ToOwnedSliceArgs)
      (pointer : Z) :
    Z.of_nat (length (arrayListItems (toOwnedList args))) =
      arrayListLength (toOwnedList args) * elementBytes ->
    pointer ↦ₘ∗ arrayListItems (toOwnedList args) -∗
    altFlBlock pointer (arrayListLength (toOwnedList args) * elementBytes) log2Align -∗
    arrayListBuffer elementBytes log2Align (toOwnedCopiedSlice args pointer).
  Proof.
    iIntros (Hlen) "Hitems Hblock".
    iDestruct (mem_mapsto_array_in_range with "Hitems") as %Hr.
    change (Z.of_N (8 `div` 8)) with 1 in Hr.
    rewrite /arrayListBuffer /toOwnedCopiedSlice /=.
    replace ((arrayListLength (toOwnedList args) - arrayListLength (toOwnedList args)) *
      elementBytes) with 0 by lia.
    rewrite mem_mapsto_uninit_0. iFrame. iPureIntro. lia.
  Qed.

  (* A saved-register cell of the frame, at the address the generated entries
     spell (the stack pointer, minus the frame, plus the slot offset). *)
  Lemma toOwned_frame_cell (sp c kb : bv 64) (frame a n : Z) :
    frame <= bv_unsigned sp -> bv_unsigned c = 2 ^ 64 - frame -> bv_unsigned kb < frame ->
    a = bv_unsigned sp - frame + bv_unsigned kb -> 8 <= n ->
    a ↦ₘ? n ⊢ (∃ w : bv 64, bv_unsigned (bv_add (bv_add sp c) kb) ↦ₘ w) ∗ (a + 8) ↦ₘ? (n - 8).
  Proof.
    intros Hsp Hc Hk -> Hn. iIntros "H".
    iDestruct (arrayList_uninit_split _ 8 with "H") as "[H $]"; [lia|].
    iDestruct (arrayList_uninit_word with "H") as (w) "H". iExists w.
    by rewrite (toOwned_frame_address sp c kb frame).
  Qed.

  Lemma toOwned_frame_uncell (sp c kb : bv 64) (frame a n : Z) (w : bv 64) :
    frame <= bv_unsigned sp -> bv_unsigned c = 2 ^ 64 - frame -> bv_unsigned kb < frame ->
    a = bv_unsigned sp - frame + bv_unsigned kb -> 0 <= n ->
    bv_unsigned (bv_add (bv_add sp c) kb) ↦ₘ w -∗ (a + 8) ↦ₘ? n -∗ a ↦ₘ? (8 + n).
  Proof.
    intros Hsp Hc Hk -> Hn. iIntros "Hw H".
    rewrite (toOwned_frame_address sp c kb frame) //.
    iDestruct (arrayList_word_uninit with "Hw") as "Hw".
    iApply (arrayList_uninit_join with "Hw H"); lia.
  Qed.

  (* A saved-register cell back to uninitialized bytes at its plain address. *)
  Lemma toOwned_cell_uninit (sp c kb : bv 64) (frame : Z) (w : bv 64) :
    frame <= bv_unsigned sp -> bv_unsigned c = 2 ^ 64 - frame -> bv_unsigned kb < frame ->
    bv_unsigned (bv_add (bv_add sp c) kb) ↦ₘ w -∗
    (bv_unsigned sp - frame + bv_unsigned kb) ↦ₘ? 8.
  Proof.
    iIntros (Hsp Hc Hk) "Hw". rewrite (toOwned_frame_address sp c kb frame) //.
    iApply (arrayList_word_uninit with "Hw").
  Qed.

  (* Two adjacent uninitialized regions, with the addresses and sizes as equations. *)
  Lemma toOwned_uninit_join_at (a b m n k : Z) :
    b = a + m -> k = m + n -> 0 <= m -> 0 <= n ->
    a ↦ₘ? m -∗ b ↦ₘ? n -∗ a ↦ₘ? k.
  Proof.
    iIntros (-> -> Hm Hn) "H1 H2". iApply (arrayList_uninit_join with "H1 H2"); lia.
  Qed.

  Lemma toOwned_uninit_at (a b n : Z) : a = b -> a ↦ₘ? n -∗ b ↦ₘ? n.
  Proof. iIntros (->) "$". Qed.
End spatial.
