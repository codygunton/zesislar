Require Import ZesuSsz.Automation.All.
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

Local Tactic Notation "hand697c_recover" integer(count) := do count zesu_liAStep.

Lemma DesignedBoundary_800d697c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)  :
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (DesignedEntry_800d697c args frameBytes x13 inputPrefix rest).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: hand697c_recover 450.
1: ZesuSsz.Automation.Hooks.zesu_liAWriteMemFocused.
Unshelve.
all: try (lazymatch goal with
| |- lithium.proof_state.SHELVED_SIDECOND (Z.of_nat _ = _) =>
  unfold lithium.proof_state.SHELVED_SIDECOND;
  lazymatch goal with |- ?P => let evidence := ZesuSsz.Automation.Hooks.zesu_registered_pure_fact P in exact evidence end
end).
all: try (lazymatch goal with
| |- lithium.proof_state.SHELVED_SIDECOND _ => shelve
| |- nat => shelve
end).
1: hand697c_recover 3.
1: liFindInContext.
1: hand697c_recover 3.
1: iSplit; [iPureIntro; lazymatch goal with |- ?P => let evidence := ZesuSsz.Automation.Hooks.zesu_registered_pure_fact P in exact evidence end | ].
1: iSplit; [iPureIntro; eapply decodeItemFlagUpdatedBaseBound; [exact HarrayFact3 | lia] | ].
1: hand697c_recover 171.
1: liFindInContext.
1: hand697c_recover 3.
1: iSplit; [iPureIntro; lazymatch goal with |- ?P => let evidence := ZesuSsz.Automation.Hooks.zesu_registered_pure_fact P in exact evidence end | ].
1: iSplit.
1: iPureIntro.
1: rewrite !length_drop !length_app !length_take !HarrayFact3.
1: cbn [length N.to_nat].
1: rewrite length_drop HarrayFact3.
1: cbn.
1: lia.
1: hand697c_recover 5.
1: unfold TRACE.
1: hand697c_recover 6.
1: assert (Hliteral : bool_decide (bv_unsigned inputPrefix <= 127) = true) by (apply bool_decide_true; exact H1).
1: liExist.
1: do 5 liExist.
1: liInst (fun x => x.1ₗ = true).
1: liExInst.
1: liInst (fun x => x.3ₗ = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1))).
1: liExInst.
1: liInst (fun x => x.3ₗ = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))).
1: liExInst.
1: zesu_block.
1: iPureIntro.
1: repeat (first [assumption | split]).
1: apply decodeItemRawInputPointer; assumption.
1: apply (decodeItemStoredPointerImage (Z_to_bv 64 (decodeItemInputPointer args)) (Z_to_bv 64 1)).
1: apply (decodeItemStoredLengthImage (Z_to_bv 64 (decodeItemInputPointer args)) (Z_to_bv 64 1)).
1: rewrite skipn_skipn.
1: apply (decodeItemRawOutputStatus (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
1: apply (decodeItemStoredWordBytes (Z_to_bv 64 (decodeItemInputPointer args))).
1: rewrite skipn_skipn.
1: apply (decodeItemRawOutputPad17 (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
1: rewrite skipn_skipn.
1: apply (decodeItemRawOutputPad34 (decodeItemBeforeStorage args) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)))); [exact HarrayFact3 | reflexivity | reflexivity].
Unshelve.
all: unfold lithium.proof_state.SHELVED_SIDECOND.
all: try reflexivity.
1: f_equal; f_equal; f_equal; apply bv_eq; reflexivity.
all: try (lazymatch goal with |- @eq valu _ _ => f_equal; f_equal; f_equal; apply bv_eq; reflexivity end).
1: f_equal.
1: apply bool_decide_true.
1: bv_solve.
1: rewrite HarrayFact3; cbn; lia.
all: f_equal; apply bool_decide_true; bv_solve.
Qed.
