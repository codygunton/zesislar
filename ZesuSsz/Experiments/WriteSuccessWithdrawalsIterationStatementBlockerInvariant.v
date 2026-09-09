From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlocker.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerRejected.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerMachine.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerMemory.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessBlockerLocal writeSuccessBlockerGlobal
  writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory.

Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerItems.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerReads.

Lemma writeSuccessBlockerInv15694Rejected :
  ~ Inv_15694 writeSuccessBlockerArgs writeSuccessBlockerSp
      writeSuccessBlockerPointer 0x20001000 2 0 2
      writeSuccessBlockerWithdrawal writeSuccessBlockerAllBytes []
      writeSuccessBlockerCurrent writeSuccessBlockerNext
      writeSuccessBlockerScratchBefore writeSuccessBlockerEncoderScratch
      writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory []
      writeSuccessBlockerState.
Proof.
  intro Hinv. unfold Inv_15694 in Hinv.
  assert (Hrepresentation : writeSuccessConcreteRepresentationOff 0x200017d0
      writeSuccessBlockerDecoded writeSuccessBlockerRepresentedMemory
      writeSuccessBlockerOwner).
  { cbn [writeSuccessBlockerState writeSuccessBlockerArgs] in Hinv.
    rewrite writeSuccessBlockerGlobalMemory in Hinv. tauto. }
  exact (writeSuccessBlockerEntryRejected Hrepresentation).
Qed.

Print Assumptions writeSuccessBlockerInv15694Rejected.
