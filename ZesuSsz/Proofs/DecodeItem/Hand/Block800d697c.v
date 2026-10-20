Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ListSplice.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.

Definition DesignedEntry_800d697c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d697c) := I.
Global Typeclasses Opaque DesignedEntry_800d697c.

Lemma DesignedBoundary_800d697c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)  :
  instr_pre 0x800d698c (∃ (successor_x11 successor_x12 successor_x13 successor_x14 successor_x15 successor_x16 : bv 64) (successor_outputBytes successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698cLiteral args successor_x11 successor_x12 successor_x13 successor_x14 successor_x15 successor_x16 successor_outputBytes successor_frameBytes successor_inputPrefix successor_rest)%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (DesignedEntry_800d697c args frameBytes x13 inputPrefix rest).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: zesu_run_until ltac:(fun _ => lazymatch goal with
| |- envs_entails _ ?P => lazymatch P with context [decodeItemEntryAt800d698cLiteral] => idtac end
end).
1: iMatchHyp ltac:(fun name resource => lazymatch resource with
  (decodeItemOutputPointer args ↦ₘ∗ ?storage)%I =>
    iExists (Z_to_bv 64 (decodeItemInputPointer args)), (Z_to_bv 64 1), (Z_to_bv 64 (bv_signed inputPrefix)), x14, x15, x16, storage, frameBytes, inputPrefix, rest end).
1: unfold decodeItemEntryAt800d698cLiteral, decodeItemReturnEntryCore;
   cbn [returnA1 returnA2 returnA3 returnA4 returnA5 returnA6 returnStorage returnFrame].
1: iFrame.
1: unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt; iFrame.
1: iSplit.
1: replace (Z_to_bv 64 1) with (1%bv : bv 64) by (apply bv_eq; reflexivity).
1: iFrame.
1: iPureIntro; repeat split; try assumption.
1: repeat first [progress rewrite length_drop | progress rewrite length_app |
 progress rewrite length_take | progress rewrite HarrayFact3 | progress cbn]; lia.
1: iPureIntro.
1: repeat (first [assumption | split]).
1: apply decodeItemRawInputPointer; assumption.
all: repeat lazymatch goal with
| |- context [ (?base + ?offset - ?base)%Z ] =>
  replace (base + offset - base)%Z with offset by lia
end.

1: rewrite <- decodeItemStoredWordBytes.
1: apply (decodeItemStoredPointerImage (Z_to_bv 64 (decodeItemInputPointer args)) (Z_to_bv 64 1)).
1: rewrite <- decodeItemStoredWordBytes.
1: apply (decodeItemStoredLengthImage (Z_to_bv 64 (decodeItemInputPointer args)) (Z_to_bv 64 1)).
all: rewrite (image_adjacent_prefix_splice _
    (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
    (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))
    8%nat 8%nat eq_refl eq_refl).
1: rewrite ?skipn_skipn.
1: apply (decodeItemRawOutputStatus (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
1: rewrite ?skipn_skipn.
1: apply (decodeItemRawOutputPad17 (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
1: rewrite ?skipn_skipn.
1: apply (decodeItemRawOutputPad34 (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
Unshelve.
all: unfold lithium.proof_state.SHELVED_SIDECOND.
all: try reflexivity.
1: f_equal; f_equal; f_equal; apply bv_eq; reflexivity.
all: try (lazymatch goal with |- @eq valu _ _ => f_equal; f_equal; f_equal; apply bv_eq; reflexivity end).
all: try solve [zesu_array_bounds_if_enabled].
all: try solve [lia].
all: f_equal; apply bool_decide_true; bv_solve.
Qed.
