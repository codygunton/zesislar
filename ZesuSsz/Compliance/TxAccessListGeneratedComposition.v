(* txAccessList compliance from its block obligations.
   The composition runs over the generated block table
   (TxAccessListBlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement tagged with its address and entry
   constant: a compiled caller lemma (TxAccessListClosedBlocks) or a field of
   TxAccessListOpenBlocks. Every entry carries the contract postcondition as K
   (txAccessListContinuation); the two return slots of the duplicated return
   block 0x04b8 take their return packages as premises, which the end bridges
   derive from K. The start bridge turns the contract entry into block
   0x0000's entry. The callee premises of the table come from the contract
   code: the four proved callees through their generated interfaces, the
   allocator and memcpy premises as they are. Hand-written by the region owner
   (model: KeysEnsureCapacityGeneratedComposition.v). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceContract.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Interfaces.KeysToOwnedSlice.
Require Import ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Import ZesuSsz.Interfaces.DecodeItemCorrect.
Require Import ZesuSsz.Interfaces.KeysEnsureCapacityCorrect.
Require Import ZesuSsz.Interfaces.KeysToOwnedSliceCorrect.
Require Import ZesuSsz.Interfaces.EntriesToOwnedSliceCorrect.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Require Import ZesuSsz.Compliance.TxAccessListExitMeaning.
Require Import ZesuSsz.Compliance.TxAccessListCompositionBoundary.
Require Import ZesuSsz.Compliance.TxAccessListBlockObligations.
Require ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode decodeItemSelectedCode
  keysEnsureCapacitySelectedCode keysToOwnedSliceSelectedCode entriesToOwnedSliceSelectedCode.

(* ---- The block form of the entry domain. ---- *)

(* The block domain adds byte-level identities of the owned cells (`rest`, the
   allocator object, the vtable) to the contract's well-formedness. *)
Lemma txAccessList_block_wellformed (args : TxAccessListArgs) :
  txAccessListArgsWellFormed args -> txAccessListBlockArgsWellFormed args.
Proof.
  intros Hwf.
  pose proof (bv_unsigned_in_range _ (txInputPointer args)) as Hp.
  pose proof (bv_unsigned_in_range _ (txInputLength args)) as Hl.
  pose proof (bv_unsigned_in_range _ (txAllocatorContext args)) as Hc.
  unfold bv_modulus in Hp, Hl, Hc. cbn [Z.of_N] in Hp, Hl, Hc.
  destruct (altFlAllocatorBytes_words (bv_unsigned (txAllocatorContext args)) Hc) as (Ha0 & Ha8).
  destruct altFlVtableBytes_words as (Hv0 & _ & Hv16 & Hv24).
  assert (Hr0 : txBlockWord (txBlockRestBytes args) 0 = bv_unsigned (txInputPointer args)).
  { unfold txBlockWord, txBlockRestBytes. cbn [Z.to_nat]. rewrite drop_0 arrayList_take8_word.
    by apply arrayList_word64Bytes_word. }
  assert (Hr8 : txBlockWord (txBlockRestBytes args) 8 = bv_unsigned (txInputLength args)).
  { unfold txBlockWord, txBlockRestBytes. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
    rewrite (arrayList_take_drop_app 8); [|reflexivity].
    rewrite take_ge; [|rewrite arrayList_word64Bytes_length; lia].
    by apply arrayList_word64Bytes_word. }
  unfold txBlockWord in Hr0, Hr8. rewrite drop_0 in Ha0 Hv0.
  revert Hwf.
  unfold txAccessListBlockArgsWellFormed, txAccessListArgsWellFormed,
    txAccessListArgsRanges, txAccessListFrameBase, txAccessListCalleeBase, txBlockWord.
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite !drop_0.
  intros H. split_and!; try tauto; try assumption; reflexivity.
Qed.

(* ---- The frame: 472 local bytes and the 13 saved-register words. ---- *)

Lemma tx_frame_address (sp c d : bv 64) :
  576 <= bv_unsigned sp -> bv_unsigned c = 18446744073709551040 -> bv_unsigned d < 576 ->
  bv_unsigned (bv_add (bv_add sp c) d) = bv_unsigned sp - 576 + bv_unsigned d.
Proof.
  intros Hsp Hc Hd. pose proof (bv_unsigned_in_range _ sp) as Hr.
  pose proof (bv_unsigned_in_range _ d) as Hdr. unfold bv_modulus in *.
  rewrite !bv_add_unsigned Hc. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  replace (bv_unsigned sp + 18446744073709551040) with
    ((bv_unsigned sp - 576) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. rewrite (Z.mod_small (bv_unsigned sp - 576)); [|lia].
  apply Z.mod_small. lia.
Qed.

Ltac tx_frame_addresses Hsp :=
  repeat match goal with
  | |- context [bv_unsigned (bv_add (bv_add ?sp ?c) ?d)] =>
      rewrite (tx_frame_address sp c d Hsp); [|reflexivity|cbn; lia]
  end;
  cbn [bv_unsigned].

Lemma tx_uninit_word_split `{!islaG Sigma} `{!threadG} (a n : Z) :
  8 <= n -> a ↦ₘ? n -∗ (∃ w : bv 64, a ↦ₘ w) ∗ (a + 8) ↦ₘ? (n - 8).
Proof.
  iIntros (Hn) "H".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W $]"; [lia|].
  by iApply arrayList_uninit_word.
Qed.

Lemma txAccessList_stack_bound (args : TxAccessListArgs) :
  txAccessListArgsWellFormed args -> 576 <= bv_unsigned (txStackPointer args).
Proof. intros ((_ & _ & _ & _ & _ & _ & _ & Hsp & _) & _). lia. Qed.

Lemma tx_frame_open `{!islaG Sigma} `{!threadG} (a : Z) :
  a ↦ₘ? 576 -∗
  a ↦ₘ? 472 ∗
  ∃ wm104 wm96 wm88 wm80 wm72 wm64 wm56 wm48 wm40 wm32 wm24 wm16 wm8 : bv 64,
   (a + 472) ↦ₘ wm104 ∗
   (a + 480) ↦ₘ wm96 ∗
   (a + 488) ↦ₘ wm88 ∗
   (a + 496) ↦ₘ wm80 ∗
   (a + 504) ↦ₘ wm72 ∗
   (a + 512) ↦ₘ wm64 ∗
   (a + 520) ↦ₘ wm56 ∗
   (a + 528) ↦ₘ wm48 ∗
   (a + 536) ↦ₘ wm40 ∗
   (a + 544) ↦ₘ wm32 ∗
   (a + 552) ↦ₘ wm24 ∗
   (a + 560) ↦ₘ wm16 ∗
   (a + 568) ↦ₘ wm8.
Proof.
  iIntros "H".
  iDestruct (arrayList_uninit_split _ 472 with "H") as "[$ H]"; [lia|].
  replace (576 - 472) with 104 by lia.
  iDestruct (tx_uninit_word_split _ 104 with "H") as "[[%wm104 Wm104] H]"; [lia|].
  replace (a + 472 + 8) with (a + 480) by lia. replace (104 - 8) with 96 by lia.
  iDestruct (tx_uninit_word_split _ 96 with "H") as "[[%wm96 Wm96] H]"; [lia|].
  replace (a + 480 + 8) with (a + 488) by lia. replace (96 - 8) with 88 by lia.
  iDestruct (tx_uninit_word_split _ 88 with "H") as "[[%wm88 Wm88] H]"; [lia|].
  replace (a + 488 + 8) with (a + 496) by lia. replace (88 - 8) with 80 by lia.
  iDestruct (tx_uninit_word_split _ 80 with "H") as "[[%wm80 Wm80] H]"; [lia|].
  replace (a + 496 + 8) with (a + 504) by lia. replace (80 - 8) with 72 by lia.
  iDestruct (tx_uninit_word_split _ 72 with "H") as "[[%wm72 Wm72] H]"; [lia|].
  replace (a + 504 + 8) with (a + 512) by lia. replace (72 - 8) with 64 by lia.
  iDestruct (tx_uninit_word_split _ 64 with "H") as "[[%wm64 Wm64] H]"; [lia|].
  replace (a + 512 + 8) with (a + 520) by lia. replace (64 - 8) with 56 by lia.
  iDestruct (tx_uninit_word_split _ 56 with "H") as "[[%wm56 Wm56] H]"; [lia|].
  replace (a + 520 + 8) with (a + 528) by lia. replace (56 - 8) with 48 by lia.
  iDestruct (tx_uninit_word_split _ 48 with "H") as "[[%wm48 Wm48] H]"; [lia|].
  replace (a + 528 + 8) with (a + 536) by lia. replace (48 - 8) with 40 by lia.
  iDestruct (tx_uninit_word_split _ 40 with "H") as "[[%wm40 Wm40] H]"; [lia|].
  replace (a + 536 + 8) with (a + 544) by lia. replace (40 - 8) with 32 by lia.
  iDestruct (tx_uninit_word_split _ 32 with "H") as "[[%wm32 Wm32] H]"; [lia|].
  replace (a + 544 + 8) with (a + 552) by lia. replace (32 - 8) with 24 by lia.
  iDestruct (tx_uninit_word_split _ 24 with "H") as "[[%wm24 Wm24] H]"; [lia|].
  replace (a + 552 + 8) with (a + 560) by lia. replace (24 - 8) with 16 by lia.
  iDestruct (tx_uninit_word_split _ 16 with "H") as "[[%wm16 Wm16] H]"; [lia|].
  replace (a + 560 + 8) with (a + 568) by lia. replace (16 - 8) with 8 by lia.
  iDestruct (arrayList_uninit_word with "H") as (wm8) "Wm8".
  iExists wm104, wm96, wm88, wm80, wm72, wm64, wm56, wm48, wm40, wm32, wm24, wm16, wm8. iFrame.
Qed.

Lemma tx_frame_close `{!islaG Sigma} `{!threadG} (a : Z) (wm104 wm96 wm88 wm80 wm72 wm64 wm56 wm48 wm40 wm32 wm24 wm16 wm8 : bv 64) :
  a ↦ₘ? 472 -∗
  (a + 472) ↦ₘ wm104 -∗
  (a + 480) ↦ₘ wm96 -∗
  (a + 488) ↦ₘ wm88 -∗
  (a + 496) ↦ₘ wm80 -∗
  (a + 504) ↦ₘ wm72 -∗
  (a + 512) ↦ₘ wm64 -∗
  (a + 520) ↦ₘ wm56 -∗
  (a + 528) ↦ₘ wm48 -∗
  (a + 536) ↦ₘ wm40 -∗
  (a + 544) ↦ₘ wm32 -∗
  (a + 552) ↦ₘ wm24 -∗
  (a + 560) ↦ₘ wm16 -∗
  (a + 568) ↦ₘ wm8 -∗
  a ↦ₘ? 576.
Proof.
  iIntros "Hl Wm104 Wm96 Wm88 Wm80 Wm72 Wm64 Wm56 Wm48 Wm40 Wm32 Wm24 Wm16 Wm8".
  iDestruct (arrayList_word_uninit with "Wm8") as "H".
  iDestruct (arrayList_word_uninit with "Wm16") as "W".
  replace (a + 568) with (a + 560 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 8) with 16 by lia.
  iDestruct (arrayList_word_uninit with "Wm24") as "W".
  replace (a + 560) with (a + 552 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 16) with 24 by lia.
  iDestruct (arrayList_word_uninit with "Wm32") as "W".
  replace (a + 552) with (a + 544 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 24) with 32 by lia.
  iDestruct (arrayList_word_uninit with "Wm40") as "W".
  replace (a + 544) with (a + 536 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 32) with 40 by lia.
  iDestruct (arrayList_word_uninit with "Wm48") as "W".
  replace (a + 536) with (a + 528 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 40) with 48 by lia.
  iDestruct (arrayList_word_uninit with "Wm56") as "W".
  replace (a + 528) with (a + 520 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 48) with 56 by lia.
  iDestruct (arrayList_word_uninit with "Wm64") as "W".
  replace (a + 520) with (a + 512 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 56) with 64 by lia.
  iDestruct (arrayList_word_uninit with "Wm72") as "W".
  replace (a + 512) with (a + 504 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 64) with 72 by lia.
  iDestruct (arrayList_word_uninit with "Wm80") as "W".
  replace (a + 504) with (a + 496 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 72) with 80 by lia.
  iDestruct (arrayList_word_uninit with "Wm88") as "W".
  replace (a + 496) with (a + 488 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 80) with 88 by lia.
  iDestruct (arrayList_word_uninit with "Wm96") as "W".
  replace (a + 488) with (a + 480 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 88) with 96 by lia.
  iDestruct (arrayList_word_uninit with "Wm104") as "W".
  replace (a + 480) with (a + 472 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W H") as "H"; [lia|lia|]. replace (8 + 96) with 104 by lia.
  iDestruct (arrayList_uninit_join with "Hl H") as "H"; [lia|lia|]. replace (472 + 104) with 576 by lia.
  iExact "H".
Qed.

Lemma txAccessList_start_bridge `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (returnAddress : Z) :
  (⌜bv_unsigned (txReturnAddress args) = returnAddress⌝ ∗ txAccessListEntryResources args) ⊢
  ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 args returnAddress.
Proof.
  rewrite /txAccessListEntryResources /ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "[%Hret (%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hin & Hrest & Halloc & Hvt & Hheap & Hscr & Hres & Hframe & Hcallee & %Hwf & _)]".
  iEval (rewrite altFlAllocatorObject_unfold) in "Halloc".
  iEval (rewrite altFlVtable_unfold) in "Hvt".
  pose proof (txAccessList_block_wellformed args Hwf) as Hbwf.
  pose proof (txAccessList_stack_bound args Hwf) as Hsp.
  unfold txAccessListFrameBase, txAccessListCalleeBase, txBlockRestBytes.
  iDestruct (tx_frame_open with "Hframe") as "(Hlocal & %wm104 & %wm96 & %wm88 & %wm80 & %wm72 & %wm64 & %wm56 & %wm48 & %wm40 & %wm32 & %wm24 & %wm16 & %wm8 & Wm104 & Wm96 & Wm88 & Wm80 & Wm72 & Wm64 & Wm56 & Wm48 & Wm40 & Wm32 & Wm24 & Wm16 & Wm8)".
  iExists x5, x6, x7, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists wm104, wm96, wm88, wm80, wm72, wm64, wm56, wm48, wm40, wm32, wm24, wm16, wm8.
  tx_frame_addresses Hsp.
  iFrame.
  iPureIntro. split_and!.
  - split; [exact Hret|exact Hbwf].
  - destruct Hwf as (_ & _ & _ & Hra & _). exact Hra.
  - apply zesu_hist_intro.
    unfold ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0_Hist.
    exists (BV 64 0). split; vm_compute; reflexivity.
Qed.

(* ---- The end bridges: each return package implies the contract postcondition. ---- *)

(* reg_col stays folded while the resources are framed. *)
#[local] Typeclasses Opaque reg_col.

Lemma tx_extract_concat8 (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) (k : N) (b : bv 8) :
  (k = 0 /\ b = b0 \/ k = 8 /\ b = b1 \/ k = 16 /\ b = b2 \/ k = 24 /\ b = b3 \/
   k = 32 /\ b = b4 \/ k = 40 /\ b = b5 \/ k = 48 /\ b = b6 \/ k = 56 /\ b = b7)%N ->
  bv_extract k 8 (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 b7 b6) b5) b4) b3) b2) b1) b0) = b.
Proof.
  intros H. Time (repeat destruct H as [[-> ->]|H]; [..|destruct H as [-> ->]]; bv_simplify; bitblast; f_equal; lia).
Qed.
Lemma tx_extract_concat2 (b0 b1 : bv 8) (k : N) (b : bv 8) :
  (k = 0 /\ b = b0 \/ k = 8 /\ b = b1)%N -> bv_extract k 8 (bv_concat 16 b1 b0) = b.
Proof. intros [[-> ->]|[-> ->]]; bv_simplify; bitblast; f_equal; lia. Qed.
Ltac tx_byte_eq :=
  first
    [ apply tx_extract_concat8; repeat (first [left; split; reflexivity | right]); split; reflexivity
    | apply tx_extract_concat2; repeat (first [left; split; reflexivity | right]); split; reflexivity
    | reflexivity ].

(* The success result of entriesToOwnedSlice: its result image names the
   slice, which holds the final list's items, the kind is success (the
   machine read error code 0). *)
Lemma tx_entries_result (final : ArrayListState) (before : list byte) (outcome : ToOwnedSliceOutcome) :
  entriesToOwnedSliceCallAllows final before outcome ->
  arrayListWellFormed entriesElementBytes final ->
  bv_unsigned (bv_concat 16 (nth 17 (toOwnedResultAfter outcome) (BV 8 0))
                 (nth 16 (toOwnedResultAfter outcome) (BV 8 0))) = 0 ->
  length before = 24%nat ->
  toOwnedResultAfter outcome =
    arrayListResultImage before (arrayListPointer (toOwnedSlice outcome)) (arrayListLength final) /\
  arrayListLength (toOwnedSlice outcome) = arrayListLength final /\
  arrayListItems (toOwnedSlice outcome) = arrayListItems final /\
  arrayListWellFormed entriesElementBytes (toOwnedSlice outcome) /\
  arrayListCapacity (toOwnedSlice outcome) = arrayListLength (toOwnedSlice outcome).
Proof.
  intros Hallows Hwf Hcode Hlen.
  destruct (entriesToOwnedSliceCallAllowsWellFormed _ _ _ Hallows) as (_ & Hwfs & Hcap).
  destruct (Z.eq_dec (arrayListLength final) 0) as [H0|H0].
  - destruct (entriesToOwnedSliceCallAllowsEmpty _ _ _ Hallows H0) as (_ & _ & Hs & Hr).
    assert (Hnil : arrayListItems final = []).
    { destruct Hwf as (_ & Hitems & _). rewrite H0 in Hitems.
      destruct (arrayListItems final); [done|cbn in Hitems; lia]. }
    rewrite Hr. rewrite Hs in Hwfs Hcap |- *. cbn. rewrite H0 Hnil. split_and!; done.
  - destruct (toOwnedKind outcome) eqn:Hk.
    + destruct (entriesToOwnedSliceCallAllowsSuccess _ _ _ Hallows H0 Hk) as (_ & Hl & Hi & Hr).
      rewrite Hr. split_and!; done.
    + destruct (entriesToOwnedSliceCallAllowsOutOfMemory _ _ _ Hallows H0 Hk) as (_ & _ & Hr).
      exfalso. rewrite Hr in Hcode. unfold arrayListErrorImage in Hcode.
      do 18 (destruct before as [|? before]; [cbn in Hlen; lia|]).
      vm_compute in Hcode. discriminate.
Qed.


Lemma tx_forall2_pad_keys (done : list AccessListEntryValue) (images : list TxAccessListEntryImage) :
  length done = length images ->
  Forall (fun image => Z.of_nat (length (imagePadding image)) = txAccessListPaddingSize) images ->
  Forall2 (fun entry image => entryKeys entry <> [] ->
    txRamRange (imageKeysPointer image) (txAccessListKeySize * Z.of_nat (length (entryKeys entry)))) done images ->
  Forall2 (fun entry image =>
    Z.of_nat (length (imagePadding image)) = txAccessListPaddingSize /\
    (entryKeys entry <> [] ->
     txRamRange (imageKeysPointer image) (txAccessListKeySize * Z.of_nat (length (entryKeys entry))))) done images.
Proof.
  intros _ Hpad Hkeys. induction Hkeys as [|e i done images Hk Hrest IH]; [constructor|].
  inversion Hpad as [|? ? Hp Hpads]; subst. constructor; [split; assumption|]. apply IH. exact Hpads.
Qed.

Lemma tx_list_length_range (eb : Z) (state : ArrayListState) :
  0 < eb -> arrayListWellFormed eb state -> 0 <= arrayListLength state < 2 ^ 64.
Proof.
  intros He (Hl & _ & _ & Hram).
  destruct (Z.eq_dec (arrayListCapacity state) 0) as [Hc|Hc]; [lia|].
  destruct (Hram ltac:(lia)) as [Hlo Hhi].
  unfold machineRamEnd in *. cbn [mapRamBase mapRamSize defaultMap] in *. nia.
Qed.

Lemma tx_x2_restore (sp : bv 64) :
  bv_add (bv_add sp (BV 64 18446744073709551040)) (BV 64 576) = sp.
Proof. bv_solve. Qed.


Lemma tx_take16_words (a b : Z) (rest : list byte) :
  take 16 (word64Bytes a ++ word64Bytes b ++ rest) = word64Bytes a ++ word64Bytes b.
Proof. reflexivity. Qed.

Lemma tx_word64At_0 (a : Z) (rest : list byte) :
  0 <= a < 2 ^ 64 -> word64At (word64Bytes a ++ rest) 0 a.
Proof.
  intros Ha. unfold word64At. cbn [skipn]. rewrite arrayList_take8_word.
  split; [reflexivity|]. rewrite <- littleEndianBv. by apply arrayList_word64Bytes_word.
Qed.

Lemma tx_word64At_8 (a b : Z) (rest : list byte) :
  0 <= b < 2 ^ 64 -> word64At (word64Bytes a ++ word64Bytes b ++ rest) 8 b.
Proof.
  intros Hb. unfold word64At.
  replace (skipn 8 (word64Bytes a ++ word64Bytes b ++ rest)) with (word64Bytes b ++ rest)
    by (rewrite skipn_app; reflexivity).
  rewrite arrayList_take8_word.
  split; [reflexivity|]. rewrite <- littleEndianBv. by apply arrayList_word64Bytes_word.
Qed.

Lemma txAccessList_end_bridge_slot1 `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (returnAddress : Z) :
  ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 args returnAddress ⊢
  txAccessListPost args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 /txAccessListPost.
  iIntros "(%x5 & %x6 & %x7 & %x12 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & %outcome & %call_after & %final & %done & %images & %scratch & %rest & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hin & Halloc & Hvt & Hheap & Hres & Hres18 & F0 & Fcall & S27 & S26 & S25 & S24 & S23 & S22 & S21 & S20 & S19 & S18 & S9 & S8 & S1 & Hcallee & Fhdr & F1 & Fres & F2 & Hkeys & Hscr & Hrest & Hlist & Hslice & %Hdom & %Hra & %Hcall & %Hwf & %Hkr & %Hscrlen & %Hhdrlen & %Hreslen & %Hscrlen2 & %Hb1 & %Hb2 & %Hhist)".
  apply zesu_hist_elim in Hhist.
  unfold ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_Hist in Hhist.
  destruct Hhist as (x21 & ms & w1 & w2 & w3 & w4 & w5 & w6 & w7 & (a13 & a14 & a15 & a16 & a17 & before & Hcd & Hcm) & Hx21 & Hlen & Hitems & Hpad & (h & p & Hdec & Hwalk & Hrestbytes) & (b13 & b14 & b15 & b16 & b17 & bscr & bctx & bres & Hetd & Heta) & Hrest_facts).
  destruct_and? Hrest_facts.
  match goal with H : bv_unsigned (bv_concat 16 (nth 17 (toOwnedResultAfter outcome) _) _) = 0 |- _ =>
    rename H into Hcode end.
  pose proof (proj2 Hdom) as Hbwf.
  pose proof (txAccessListBlockArgsWellFormed_contract _ Hbwf) as Hcwf.
  pose proof (txAccessList_stack_bound _ Hcwf) as Hsp.
  pose proof (entriesToOwnedSliceCallDomainResultLength _ _ _ _ _ Hetd) as Hbres.
  destruct (tx_entries_result final bres outcome Heta Hwf Hcode Hbres) as (HR & Hsl & Hsi & Hswf & Hscap).
  remember (toOwnedResultAfter outcome) as R eqn:HRdef.
  lazymatch iTypeOf (INamed "Hres") with
  | Some (_, ?f ?L) => assert (HL : L = firstn 16 R ++ [BV 8 0; BV 8 0])
  end.
  { clear - Hreslen.
    do 24 (destruct R as [|? R]; [cbn in Hreslen; lia|]).
    destruct R; [|cbn in Hreslen; lia].
    cbn [firstn nth app]. repeat f_equal; tx_byte_eq. }
  rewrite HL. clear HL.
  (* the frame: its pieces as uninitialised bytes, joined, then as bytes *)
  iDestruct (arrayList_bytes_uninit with "Fcall") as "Fcall". rewrite Hcall.
  iDestruct (arrayList_bytes_uninit with "Fhdr") as "Fhdr". rewrite Hhdrlen.
  iDestruct (arrayList_bytes_uninit with "Fres") as "Fres". rewrite Hreslen.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  iDestruct (arrayList_uninit_join with "F0 Fcall") as "Fl"; [lia|lia|].
  replace (bv_unsigned (txStackPointer args) - 448) with (bv_unsigned (txStackPointer args) - 576 + (88 + 40)) by lia.
  iDestruct (arrayList_uninit_join with "Fl Fhdr") as "Fl"; [lia|lia|].
  replace (bv_unsigned (txStackPointer args) - 424) with (bv_unsigned (txStackPointer args) - 576 + (88 + 40 + 24)) by lia.
  iDestruct (arrayList_uninit_join with "Fl F1") as "Fl"; [lia|lia|].
  replace (bv_unsigned (txStackPointer args) - 576 + (88 + 40 + 24) + 288) with (bv_unsigned (txStackPointer args) - 576 + (88 + 40 + 24 + 288)) by lia.
  iDestruct (arrayList_uninit_join with "Fl Fres") as "Fl"; [lia|lia|].
  replace (bv_unsigned (txStackPointer args) - 576 + (88 + 40 + 24) + 312) with (bv_unsigned (txStackPointer args) - 576 + (88 + 40 + 24 + 288 + 24)) by lia.
  iDestruct (arrayList_uninit_join with "Fl F2") as "Fl"; [lia|lia|].
  replace (88 + 40 + 24 + 288 + 24 + 8) with 472 by lia.
  tx_frame_addresses Hsp.
  iDestruct (tx_frame_close with "Fl S27 S26 S25 S24 S23 S22 S21 S20 S19 S18 S9 S8 S1") as "Fl".
  iDestruct (zesu_uninit_bytes _ 576 576 with "Fl") as (frame Hframe) "Fl"; [done|].
  (* the result: its 18 written bytes and the 6 untouched ones *)
  iDestruct (zesu_uninit_bytes _ 6 6 with "Hres18") as (pad Hpadlen) "Hres18"; [done|].
  iDestruct (zesu_byte_array_join_sized _ _ _ _ _ 18 6 24 with "Hres Hres18") as "[Hres %Hreslen2]".
  { rewrite length_app firstn_length Hreslen. done. }
  { exact Hpadlen. } { lia. } { lia. }
  (* the returned entries slice *)
  pose proof Hswf as (_ & Hsitems & Hsptr & Hsram).
  iDestruct (big_sepL2_length with "Hkeys") as %Hkl.
  iAssert (txOwnedSlice (arrayListPointer (toOwnedSlice outcome)) txAccessListEntriesLog2Align
             (txAccessListEntriesBytes done images))%I with "[Hslice]" as "Hown".
  { rewrite /txOwnedSlice arrayListBuffer_unfold. iDestruct "Hslice" as "(Hitems & _ & Hblock)".
    rewrite Hsi Hitems in Hsitems |- *.
    destruct (txAccessListEntriesBytes done images) as [|b bs] eqn:Hb; [done|].
    iFrame "Hitems". rewrite Hscap Hsl. rewrite Hsl in Hsitems.
    replace (Z.of_nat (length (b :: bs))) with (arrayListLength final * 40) by lia.
    iExact "Hblock". }
  pose proof (tx_list_length_range 40 final ltac:(lia) Hwf) as Hlenr.
  lazymatch iTypeOf (INamed "Hscr") with
  | Some (_, ?f ?S) =>
  iExists {| txOutcomeClass := txAccessListOk done; txConsumed := h + p;
             txResultBytes := (take 16 R ++ [BV 8 0; BV 8 0]) ++ pad;
             txAfterFrame := frame; txScratchAfter := S;
             txEntriesPointer := arrayListPointer (toOwnedSlice outcome);
             txEntryImages := images; txLeakedBlocks := [] |}
  end.
  iSplit.
  { iPureIntro. cbn [islarisContractAllows txAccessListContractModel].
    split; [exact (proj1 Hdom)|].
    unfold txAccessListAllows; cbn [txOutcomeClass txConsumed txResultBytes txAfterFrame
      txScratchAfter txEntriesPointer txEntryImages txLeakedBlocks].
    split_and!.
    - exact (txAccessList_success_meaning args h p done Hcwf Hdec Hwalk).
    - unfold txAccessListResultImage; cbn [txOutcomeClass txResultBytes txEntriesPointer].
      rewrite HR. unfold arrayListResultImage. rewrite tx_take16_words -!app_assoc.
      split_and!.
      + rewrite !length_app !arrayList_word64Bytes_length. cbn [length]. lia.
      + apply tx_word64At_0. lia.
      + rewrite -Hlen. apply tx_word64At_8. lia.
      + unfold byteAt. reflexivity.
      + unfold byteAt. reflexivity.
    - unfold txAccessListHeapImage; cbn [txOutcomeClass txEntryImages txLeakedBlocks txEntriesPointer].
      split_and!; [lia|done| |].
      + intros Hne. destruct (Hsram ltac:(destruct done; [done|cbn in Hlen; lia])) as [Hlo Hhi].
        unfold txRamRange. unfold machineRamEnd in *. cbn [mapRamBase mapRamSize defaultMap] in *. lia.
      + apply tx_forall2_pad_keys; [lia|exact Hpad|exact Hkr].
    - lia.
    - rewrite Hscrlen2. reflexivity. }
  rewrite /txAccessListExitResources /txAccessListReturnedHeap.
  cbn [txOutcomeClass txConsumed txResultBytes txAfterFrame txScratchAfter txEntriesPointer
    txEntryImages txLeakedBlocks].
  iExists x5, x6, x7, _, _, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  rewrite tx_x2_restore altFlAllocatorObject_unfold altFlVtable_unfold Hrestbytes.
  unfold txAccessListFrameBase, txAccessListCalleeBase.
  rewrite /txAccessListKeysSlices.
  iFrame. done.
Qed.

Lemma tx_error_result_bytes :
  [BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0;
   BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0;
   BV 8 3; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0] =
  word64Bytes 0 ++ word64Bytes 0 ++ word64Bytes txAccessListInvalidBlockCode.
Proof. unfold word64Bytes. cbn. repeat f_equal; apply bv_eq; reflexivity. Qed.

Lemma txAccessList_end_bridge_slot0 `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (returnAddress : Z) :
  ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 args returnAddress ⊢
  txAccessListPost args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 /txAccessListPost.
  iIntros "(%x5 & %x6 & %x7 & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & %call_after & %scratch & %rest & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hin & Halloc & Hvt & Hheap & Hres & F0 & Fcall & F1 & S27 & S26 & S25 & S24 & S23 & S22 & S21 & S20 & S19 & S18 & S9 & S8 & S1 & Hcallee & Hscr & Hrest & %Hdom & %Hra & %Hcall & %Hscrlen & %Hcons & %Hb1 & %Hb2 & _)".
  destruct Hcons as (consumed & Hrestbytes & Hallowed).
  pose proof (proj2 Hdom) as Hbwf.
  pose proof (txAccessListBlockArgsWellFormed_contract _ Hbwf) as Hcwf.
  pose proof (txAccessList_stack_bound _ Hcwf) as Hsp.
  destruct (txAccessList_error_meaning args consumed Hcwf Hallowed) as (cls & Hcls & Hmeaning).
  rewrite tx_error_result_bytes.
  (* the frame *)
  iDestruct (arrayList_bytes_uninit with "Fcall") as "Fcall". rewrite Hcall.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  iDestruct (arrayList_uninit_join with "F0 Fcall") as "Fl"; [lia|lia|].
  replace (bv_unsigned (txStackPointer args) - 576 + 128) with (bv_unsigned (txStackPointer args) - 576 + (88 + 40)) by lia.
  iDestruct (arrayList_uninit_join with "Fl F1") as "Fl"; [lia|lia|].
  replace (88 + 40 + 344) with 472 by lia.
  tx_frame_addresses Hsp.
  iDestruct (tx_frame_close with "Fl S27 S26 S25 S24 S23 S22 S21 S20 S19 S18 S9 S8 S1") as "Fl".
  iDestruct (zesu_uninit_bytes _ 576 576 with "Fl") as (frame Hframe) "Fl"; [done|].
  iExists {| txOutcomeClass := cls; txConsumed := consumed;
             txResultBytes := word64Bytes 0 ++ word64Bytes 0 ++ word64Bytes txAccessListInvalidBlockCode;
             txAfterFrame := frame; txScratchAfter := scratch;
             txEntriesPointer := 0; txEntryImages := []; txLeakedBlocks := [] |}.
  iSplit.
  { iPureIntro. cbn [islarisContractAllows txAccessListContractModel].
    split; [exact (proj1 Hdom)|].
    unfold txAccessListAllows; cbn [txOutcomeClass txConsumed txResultBytes txAfterFrame
      txScratchAfter txEntriesPointer txEntryImages txLeakedBlocks].
    split_and!; [exact Hmeaning| | |lia|exact Hscrlen].
    - unfold txAccessListResultImage. cbn [txOutcomeClass txResultBytes].
      split; [reflexivity|]. destruct Hcls as [->| ->]; reflexivity.
    - unfold txAccessListHeapImage. cbn [txOutcomeClass txEntryImages txLeakedBlocks].
      destruct Hcls as [->| ->]; (split; [reflexivity|apply Forall_nil]). }
  rewrite /txAccessListExitResources /txAccessListReturnedHeap.
  cbn [txOutcomeClass txConsumed txResultBytes txAfterFrame txScratchAfter txEntriesPointer
    txEntryImages txLeakedBlocks].
  iExists x5, x6, x7, _, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  rewrite tx_x2_restore altFlAllocatorObject_unfold altFlVtable_unfold Hrestbytes.
  unfold txAccessListFrameBase, txAccessListCalleeBase.
  iFrame. destruct Hcls as [->| ->]; cbn; iSplit; done.
Qed.

(* ---- Composition over the block table. ---- *)

Lemma tx_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* A return slot: its caller is used at K = emp, and K (the contract
   postcondition) gives the caller's return-package premise. *)
Lemma tx_return_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

(* The membership of a slot: address and state both match; the index is
   found syntactically (no unification against the other entries). *)
Ltac tx_index entry entries :=
  lazymatch entries with
  | entry :: _ => constr:(0%nat)
  | _ :: ?rest => let n := tx_index entry rest in constr:(S n)
  end.
Ltac tx_member :=
  lazymatch goal with
  | |- ?entry ∈ ?entries =>
      let n := tx_index entry entries in
      exact (elem_of_list_lookup_2 entries n entry eq_refl)
  end.

(* A premise is chosen by its address: callee specs by their symbols, a
   successor by table lookup; a return premise (address returnAddress, a
   variable) is no table slot and fails at once. *)
Ltac tx_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre ?a _) =>
      tryif is_var a then fail else
      tryif (let s := constr:(sym_rlp_decodeItem) in constr_eq a s) then iExact "Hdi" else
      tryif (let s := constr:(sym_array_list_Aligned_32_u8_null_ensureTotalCapacity) in constr_eq a s) then iExact "Hkec" else
      tryif (let s := constr:(sym_array_list_Aligned_32_u8_null_toOwnedSlice) in constr_eq a s) then iExact "Hkto" else
      tryif (let s := constr:(sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice) in constr_eq a s) then iExact "Heto" else
      tryif (let s := constr:(sym_alt_fl_alloc_alloc) in constr_eq a s) then iExact "Halloc" else
      tryif (let s := constr:(sym_alt_fl_alloc_remap) in constr_eq a s) then iExact "Hremap" else
      tryif (let s := constr:(sym_alt_fl_alloc_free) in constr_eq a s) then iExact "Hfree" else
      tryif (let s := constr:(sym_memcpy) in constr_eq a s) then iExact "Hmemcpy" else
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold txAccessListBlockTable; cbn [block_table_entries];
              tx_member ]
  | |- _ => iExact "Hsel"
  end.

(* The return premise of a return package from the contract continuation:
   the end bridge of the package (chosen by its name) gives the contract exit. *)
Ltac tx_exit_premise H :=
  iEval (rewrite /txAccessListContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1;
  iIntros "[Hexit _]";
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (txAccessList_end_bridge_slot0 with "Hexit")
  | Some (_, @ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (txAccessList_end_bridge_slot1 with "Hexit")
  end.

Ltac tx_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold txAccessListBlockTable; cbn [block_table_code];
         unfold txAccessListTableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Hdi & Hkec & Hkto & Heto & Halloc & Hremap & Hfree & Hmemcpy)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : txAccessListBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold txAccessListBlockAt in statement;
          first
          [ iApply tx_body_weaken; iApply statement; tx_premise
          | iApply tx_return_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ tx_exit_premise "Hret" | tx_premise .. ] ]
      end
  end.

Ltac tx_block_statements Sigma Hopen :=
  pose proof txAccessListClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

Lemma txAccessList_entry_body `{!islaG Sigma} `{!threadG} :
  TxAccessListOpenBlocks ->
  forall (args : TxAccessListArgs) (returnAddress : Z),
  ⊢ □ txAccessListTableCode -∗
    instr_body sym_rlp_decode_txAccessList
      (ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress
        (txAccessListContinuation args returnAddress)).
Proof.
  intros Hopen args returnAddress.
  tx_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (txAccessListBlockTable args returnAddress)).
  { unfold txAccessListBlockTable; cbn [block_table_entries]. tx_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold txAccessListBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: tx_slot.
Qed.

(* ---- The callee premises of the table, from the contract code. ---- *)

Lemma tx_decodeItem_boxed `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ □ instr_pre sym_rlp_decodeItem decodeItemCallSpec2.
Proof.
  iIntros "#Hcode". iModIntro. iApply instr_pre_to_body. iNext.
  iApply decodeItemCallSpec2_correct. iExact "Hcode".
Qed.

Lemma tx_keysEnsureCapacity_boxed `{!islaG Sigma} `{!threadG} :
  keysEnsureCapacitySelectedCode -∗
  □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec -∗
  □ instr_pre sym_memcpy ziskMemcpyCallSpec -∗
  □ instr_pre sym_array_list_Aligned_32_u8_null_ensureTotalCapacity keysEnsureCapacityCallSpec2.
Proof.
  iIntros "#Hcode #Ha #Hr #Hf #Hm". iModIntro. iApply instr_pre_to_body. iNext.
  iApply keysEnsureCapacityCallSpec2_correct.
  rewrite /keysEnsureCapacityContractCode /altFlAllocatorPremises /altFlAllocCallPremise /altFlRemapCallPremise
    /altFlFreeCallPremise /ziskMemcpyCallPremise.
  iFrame "#".
Qed.

Lemma tx_keysToOwnedSlice_boxed `{!islaG Sigma} `{!threadG} :
  keysToOwnedSliceSelectedCode -∗
  □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec -∗
  □ instr_pre sym_memcpy ziskMemcpyCallSpec -∗
  □ instr_pre sym_array_list_Aligned_32_u8_null_toOwnedSlice keysToOwnedSliceCallSpec2.
Proof.
  iIntros "#Hcode #Ha #Hr #Hf #Hm". iModIntro. iApply instr_pre_to_body. iNext.
  iApply keysToOwnedSliceCallSpec2_correct.
  rewrite /keysToOwnedSliceContractCode /altFlAllocatorPremises /altFlAllocCallPremise /altFlRemapCallPremise
    /altFlFreeCallPremise /ziskMemcpyCallPremise.
  iFrame "#".
Qed.

Lemma tx_entriesToOwnedSlice_boxed `{!islaG Sigma} `{!threadG} :
  entriesToOwnedSliceSelectedCode -∗
  □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec -∗
  □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec -∗
  □ instr_pre sym_memcpy ziskMemcpyCallSpec -∗
  □ instr_pre sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice entriesToOwnedSliceCallSpec2.
Proof.
  iIntros "#Hcode #Ha #Hr #Hf #Hm". iModIntro. iApply instr_pre_to_body. iNext.
  iApply entriesToOwnedSliceCallSpec2_correct.
  rewrite /entriesToOwnedSliceContractCode /altFlAllocatorPremises /altFlAllocCallPremise /altFlRemapCallPremise
    /altFlFreeCallPremise /ziskMemcpyCallPremise.
  iFrame "#".
Qed.

(* ---- The theorem, from the open blocks. ---- *)
Theorem txAccessListComplianceFrom :
  TxAccessListOpenBlocks ->
  TxAccessListContractCorrect.
Proof.
  intros Hopen returnAddress Sigma HG HT.
  change (⊢ txAccessListContractCode -∗ ∀ args : TxAccessListArgs,
    instr_body sym_rlp_decode_txAccessList
      ((⌜bv_unsigned (txReturnAddress args) = returnAddress⌝ ∗ txAccessListEntryResources args) ∗
       instr_pre returnAddress (txAccessListPost args returnAddress)))%I.
  iIntros "Hcode" (args).
  rewrite /txAccessListContractCode.
  iDestruct "Hcode" as "(#Hsel & #Hkec & #Hkto & #Heto & #Hdi & Hmemcpy & Halloc & Hremap & Hfree)".
  iPoseProof (tx_decodeItem_boxed with "Hdi") as "#Hdi2".
  iEval (rewrite /altFlAllocCallPremise) in "Halloc". iDestruct "Halloc" as "#Halloc".
  iEval (rewrite /altFlRemapCallPremise) in "Hremap". iDestruct "Hremap" as "#Hremap".
  iEval (rewrite /altFlFreeCallPremise) in "Hfree". iDestruct "Hfree" as "#Hfree".
  iEval (rewrite /ziskMemcpyCallPremise) in "Hmemcpy". iDestruct "Hmemcpy" as "#Hmemcpy".
  iPoseProof (tx_keysEnsureCapacity_boxed with "Hkec Halloc Hremap Hfree Hmemcpy") as "#Hkec2".
  iPoseProof (tx_keysToOwnedSlice_boxed with "Hkto Halloc Hremap Hfree Hmemcpy") as "#Hkto2".
  iPoseProof (tx_entriesToOwnedSlice_boxed with "Heto Halloc Hremap Hfree Hmemcpy") as "#Heto2".
  iPoseProof (txAccessList_entry_body Hopen args returnAddress with "[]") as "Hbody".
  { iModIntro. rewrite /txAccessListTableCode. iFrame "#". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hexit]".
  rewrite /ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000 /txAccessListContinuation.
  iSplitL "Hentry"; [by iApply txAccessList_start_bridge|].
  iExact "Hexit".
Qed.
