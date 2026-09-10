From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBinding.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLoopInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLoopRecords.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Open Scope Z_scope.

Lemma loop_15694 :
  forall remaining args sp pointer base total processed withdrawal allBytes
      prefix current suffix scratch encoderScratch registerFrame memoryFrame
      priorLog state,
    remaining <> 0%nat ->
    Inv_15694 args sp pointer base total processed remaining withdrawal
      allBytes prefix current suffix scratch encoderScratch registerFrame
      memoryFrame priorLog state ->
    exists segments after records,
      IslaInstructionRun (410 * remaining) state.1 segments after.1 /\
      after.2 = priorLog ++ records /\
      writeSuccessWithdrawalLoopRecords sp
        (firstn remaining (skipn processed (observationWithdrawals
          (successDecoded WriteSuccessObservation args)))) records /\
      Inv_156e8 args sp
        (pointer + Z_to_bv 64 (48 * Z.of_nat remaining))%bv base total allBytes
        registerFrame memoryFrame (priorLog ++ records) after.
Proof.
  intros remaining.
  exact (writeSuccessWithdrawalsLoopFromBlocks remaining block_15694_iteration
    block_15694_last_iteration).
Qed.

Print Assumptions loop_15694.
