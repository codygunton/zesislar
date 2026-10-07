Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import isla.riscv64.riscv64.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.LowMask.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import ZesuSsz.Automation.Switches.ListWitness.
Require Import ZesuSsz.Automation.Switches.TupleWitness.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Automation.Switches.PureWitnessConstraints.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.

Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
Require Import ZesuSsz.Automation.Switches.StrictSigned.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Lemma decodeItemJoin6ae0From6ad8_correct `{!islaG Sigma} `{!threadG}
 args (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64)
 (inputPrefix : byte) (rest : list byte) :
 ⊢ decodeItemJoin6ae0From6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
Proof.
 unfold decodeItemJoin6ae0From6ad8, decodeItemJoinTransferObligation.
 iIntros "Hcode". iEval (unfold decodeItemSelectedCode) in "Hcode".
 iDestruct "Hcode" as "#Hcode".
 zesu_run_until ltac:(fun _ => lazymatch goal with
 |- envs_entails _ (WPasm a800d6adc.a800d6adc) => idtac end).
 match goal with Hfold : RlpDecodeItemByteFold.decodeItemByteFoldFacts _ _ _ _ _ |- _ =>
   pose proof (decodeItem_fold_exit args n payloadStart lengthBytes Hfold) as [Hacc Hstart] end.
 assert (Hsum : LET0 = Z_to_bv 64 (bigEndian lengthBytes + n + 1)) by
   (unLET; rewrite Hacc; bv_solve).
 match goal with Hfits : RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits _ _ _ = false |- _ =>
   pose proof Hfits as HfoldReject;
   unfold RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits in Hfits;
   apply Z.leb_gt in Hfits; rewrite -Hsum in Hfits end.
 assert (Hsigned : bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) < bv_signed (bv_zero_extend 128 LET0)) by bv_solve.
 zesu_run_until ltac:(fun _ => first [match goal with
   Hlt : ?left < ?right, Hge : ?left >= ?right |- _ => exfalso;
     exact ((proj1 (Z.lt_nge left right) Hlt) (Z.ge_le left right Hge)) end |
   match goal with Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes) end]).
Unshelve.
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ => vm_compute in Hbad; discriminate end].
all: prepare_sidecond.
all: try solve [zesu_finish | zesu_pure_fact_hints_if_enabled | reflexivity | bv_solve].
Qed.
