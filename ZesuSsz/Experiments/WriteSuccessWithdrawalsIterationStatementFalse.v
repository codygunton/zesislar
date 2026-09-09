From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerInvariant.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerContradiction.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessBlockerRepresentedMemory writeSuccessBlockerRegs
  writeSuccessBlockerGlobal writeSuccessBlockerLocal.

Theorem writeSuccessBlock15694OldCounterexampleRejected :
  ~ Inv_15694 writeSuccessBlockerArgs writeSuccessBlockerSp
      writeSuccessBlockerPointer 0x20001000 2 0 2
      writeSuccessBlockerWithdrawal writeSuccessBlockerAllBytes []
      writeSuccessBlockerCurrent writeSuccessBlockerNext
      writeSuccessBlockerScratchBefore writeSuccessBlockerEncoderScratch
      writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory []
      writeSuccessBlockerState.
Proof. exact writeSuccessBlockerInv15694Rejected. Qed.

Print Assumptions writeSuccessBlock15694OldCounterexampleRejected.
