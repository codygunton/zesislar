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

Theorem writeSuccessBlock15694IterationStatementFalse :
  ~ block_15694_iteration_statement.
Proof.
  intro Hblock. unfold block_15694_iteration_statement in Hblock.
  have Hpre : Inv_15694 writeSuccessBlockerArgs writeSuccessBlockerSp
      writeSuccessBlockerPointer 0x20001000 2 0 2
      writeSuccessBlockerWithdrawal writeSuccessBlockerAllBytes []
      writeSuccessBlockerCurrent (writeSuccessBlockerNext ++ [])
      writeSuccessBlockerScratchBefore writeSuccessBlockerEncoderScratch
      writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory []
      writeSuccessBlockerState.
  { rewrite app_nil_r. exact writeSuccessBlockerInv15694. }
  specialize (Hblock writeSuccessBlockerArgs writeSuccessBlockerSp
    writeSuccessBlockerPointer 0x20001000 2%nat 0%nat 0%nat
    writeSuccessBlockerWithdrawal writeSuccessBlockerNextWithdrawal
    writeSuccessBlockerAllBytes [] writeSuccessBlockerCurrent
    writeSuccessBlockerNext [] writeSuccessBlockerScratchBefore
    writeSuccessBlockerEncoderScratch writeSuccessBlockerRegs
    writeSuccessBlockerRepresentedMemory [] writeSuccessBlockerState
    Hpre eq_refl eq_refl).
  destruct Hblock as
    (segments & after & records & padding & encoderAfter & Hrun & Hlog &
      Hrecords & Hpadding & HcurrentShape & Hscratch & HafterInv).
  have Hrepresentation : writeSuccessConcreteRepresentation
      (successDecoded WriteSuccessObservation writeSuccessBlockerArgs)
      after.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation writeSuccessBlockerArgs).
  { unfold Inv_15694 in HafterInv. tauto. }
  have HmemoryFrame : writeSuccessWithdrawalsMemoryFrame
      writeSuccessBlockerSp after.1.2.(seq_mem)
      writeSuccessBlockerRepresentedMemory.
  { unfold Inv_15694 in HafterInv. tauto. }
  change (writeSuccessConcreteRepresentation writeSuccessBlockerDecoded
    after.1.2.(seq_mem) writeSuccessBlockerOwner) in Hrepresentation.
  rewrite writeSuccessBlockerScratchAddress in Hscratch.
  exact (writeSuccessBlockerRequiredPostContradiction after.1.2.(seq_mem)
    Hrepresentation HmemoryFrame Hscratch).
Qed.

Print Assumptions writeSuccessBlock15694IterationStatementFalse.
