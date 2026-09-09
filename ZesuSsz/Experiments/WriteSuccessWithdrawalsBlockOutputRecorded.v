From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutput.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma block_write_output_recorded data size returnAddress bytes priorLog state :
  Inv_write_output data size returnAddress bytes priorLog state ->
  exists segments regs global,
    WriteSuccessWithdrawalsRecordedRun 5 state segments
      (writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
         returnAddress,
       priorLog ++ writeSuccessWithdrawalsOutputRecordsExact global data size) /\
    state.1 = writeSuccess10190Before regs global /\
    writeSuccessOutputRecords data size bytes
      (writeSuccessWithdrawalsOutputRecordsExact global data size).
Proof.
  intros Hinv.
  destruct (block_write_output data size returnAddress bytes priorLog state
    Hinv) as
    (segments & after & records & Hmachine & Hpc & Hlog & Houtput).
  set (recordedAfter :=
    (after.1,
     state.2 ++ segmentRecords state.1 (flattenMicroObservations segments))).
  have Hrecorded :
      WriteSuccessWithdrawalsRecordedRun 5 state segments recordedAfter.
  { split; first exact Hmachine. unfold recordedAfter. reflexivity. }
  destruct (block_write_output_recorded_covered_exact data size returnAddress
    bytes priorLog state segments recordedAfter Hinv Hrecorded) as
    (regs & global & Hentry & Hendpoint & HexactOutput).
  exists segments, regs, global. rewrite <- Hendpoint.
  split; first exact Hrecorded. split; assumption.
Qed.

Print Assumptions block_write_output_recorded.
