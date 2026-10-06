Require Import ZesuSsz.Automation.All.
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
   pose proof Hfold as HfoldBounds;
   pose proof (decodeItem_fold_exit args n payloadStart lengthBytes Hfold) as [Hacc Hstart] end.
 assert (Hsum : LET0 = Z_to_bv 64 (bigEndian lengthBytes + n + 1)) by
   (unLET; rewrite Hacc; bv_solve).
 match goal with Hfits : RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits _ _ _ = false |- _ =>
   unfold RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits in Hfits;
   apply Z.leb_gt in Hfits; rewrite -Hsum in Hfits end.
 assert (Hsigned : bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) < bv_signed (bv_zero_extend 128 LET0)) by bv_solve.
 match goal with Hdomain : decodeItemC1BDomain args |- _ => pose proof Hdomain as Hfacts end.
 assert (HdomainAt : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) by (split; [reflexivity | assumption]).
 pose proof (decodeItemDomainInputLengthBounds args Hfacts) as Hbounds.
 assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by (unfold word64Modulus; lia).
 unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hfacts.
 assert (Hstorage : length (decodeItemBeforeStorage args) = 40%nat) by tauto.
 assert (HinputLength : decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args))) by tauto.
 assert (Hrejected : decodeItemRejectedFacts args) by
   (eapply (decodeItemLongListPayloadRejected args inputPrefix rest n payloadStart lengthBytes);
    [assumption | assumption | unfold RlpDecodeItemByteFold.decodeItemByteFoldFacts in HfoldBounds; rewrite -HinputLength; lia |];
    rewrite -HinputLength;
    match goal with Hreject : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) < bv_unsigned LET0 |- _ =>
      rewrite (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) Hsum Z_to_bv_unsigned in Hreject;
      replace (bigEndian lengthBytes + n + 1) with (1 + n + bigEndian lengthBytes) in Hreject by ring;
      exact Hreject end).
 zesu_run_until ltac:(fun _ => first [match goal with
   Hlt : ?left < ?right, Hge : ?left >= ?right |- _ => exfalso;
     exact ((proj1 (Z.lt_nge left right) Hlt) (Z.ge_le left right Hge)) end |
   match goal with Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes) end]).
Unshelve.
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ => vm_compute in Hbad; discriminate end].
all: prepare_sidecond.
all: try solve [reflexivity | bv_solve].
Qed.
Print Assumptions decodeItemJoin6ae0From6ad8_correct.
