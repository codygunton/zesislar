Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.LowMask.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import ZesuSsz.Automation.Switches.StackWrite.
Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
From iris.proofmode Require Import environments.
Open Scope Z_scope.

Lemma decodeItemJoin6ae0From6970_correct `{!islaG Sigma} `{!threadG} args :
  ⊢ decodeItemJoin6ae0From6970 args.
Proof.
  unfold decodeItemJoin6ae0From6970, decodeItemJoinTransferObligation.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    |- envs_entails _ (WPasm a800d6970.a800d6970) => idtac end).
  match goal with Hdomain : decodeItemC1BDomain args |- _ =>
    pose proof Hdomain as Hfacts end.
  assert (HdomainAt : decodeItemDomainAt (decodeItemReturnAddress args)
    decodeItemC1BDomain args) by (split; [reflexivity | assumption]).
  assert (Hstorage : length (decodeItemBeforeStorage args) = 40%nat) by exact (proj1 (proj2 (decodeItemDomainFoldDerivedFacts args Hfacts))).
  assert (Hempty : decodeItemInputBytes args = []) by
    (unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hfacts;
     destruct Hfacts as [Hbytes _]; apply length_zero_iff_nil; lia).
  pose proof (decodeItemEmptyInputRejected args Hempty) as Hrejected.
  match goal with Hdomain : decodeItemC1BDomain args |- _ =>
    pose proof (decodeItemSavedFrameFacts_machine_words args Hdomain) as Hframe end.
  assert (Hzero : Z_to_bv 64 (decodeItemInputLength args) = (0%bv : bv 64))
    by bv_solve.
  zesu_run_until ltac:(fun _ => match goal with
    Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes) end).
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ =>
    vm_compute in Hbad; discriminate end].
all: zesu_expose_environment_alias.
all: zesu_run.
Unshelve.
all: try exact (bv_to_little_endian 8 8 (bv_unsigned (decodeItemSavedFramePointer args)) ++
  bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args))))%list.
all: try solve [zesu_run].
all: prepare_sidecond.
all: try solve [reflexivity | assumption | lia |
  (unfold RlpDecodeItem.decodeItemStackBytes; bv_solve)].
Qed.

Print Assumptions decodeItemJoin6ae0From6970_correct.
