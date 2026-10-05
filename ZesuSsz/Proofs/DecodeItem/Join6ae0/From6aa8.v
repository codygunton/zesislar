Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
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
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.Switches.RecordWitness.

Lemma decodeItemJoin6ae0From6aa8_correct `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From6aa8 args frameBytes prefix inputPrefix rest.
Proof.
  unfold decodeItemJoin6ae0From6aa8, decodeItemJoinTransferObligation.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    |- envs_entails _ (WPasm a800d6ab0.a800d6ab0) => idtac end).
  match goal with Hdomain : decodeItemDomainAt _ _ args |- _ =>
    pose proof Hdomain as Hfacts end.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hfacts)) as HlengthBounds.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed in Hfacts.
  assert (Hstorage : length (decodeItemBeforeStorage args) = 40%nat) by tauto.
  assert (Hheader : bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 9)) =
    bv_unsigned inputPrefix - 247) by bv_solve.
  assert (Hbyte : bv_unsigned LET2 = bv_unsigned
    (Z_to_bv 8 (bv_unsigned prefix + 9))) by (unLET; bv_solve).
  assert (Hunsigned : bv_unsigned LET2 >= bv_unsigned
    (Z_to_bv 64 (decodeItemInputLength args))) by
    (rewrite Hbyte (Z_to_bv_small 64 (decodeItemInputLength args) Hlen); lia).
  assert (Hrejected : decodeItemRejectedFacts args) by
    (eapply (decodeItemLongListHeaderRejected args inputPrefix rest); [unfold decodeItemC1BDomain, decodeItemArgsWellFormed; tauto |
      assumption | split; assumption |]; match goal with Hguard : bv_unsigned (Z_to_bv 8 _) >= _ |- _ => pose proof Hguard as HrejectionBound; rewrite Hheader in HrejectionBound end;
      assert (HinputLength : decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args))) by tauto;
      rewrite -HinputLength Z.add_1_l; apply (proj2 (Z.lt_succ_r _ _));
      apply Z.ge_le; exact HrejectionBound).
  pose proof (decodeItemErrorUnsignedComparison LET2
    (Z_to_bv 64 (decodeItemInputLength args)) Hunsigned) as Hsigned.
  zesu_run_until ltac:(fun _ => match goal with
    Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes) end).
Unshelve.
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ =>
    vm_compute in Hbad; discriminate end].
all: prepare_sidecond.
all: try solve [reflexivity | bv_solve].
Qed.

Print Assumptions decodeItemJoin6ae0From6aa8_correct.
