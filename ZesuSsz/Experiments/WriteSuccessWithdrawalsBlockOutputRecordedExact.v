From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Definition writeSuccessWithdrawalsOutputRecordsExact
    (global : seq_global_state) (data size : bv 64) :=
  [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
   (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))].

Lemma block_write_output_recorded_covered_exact data size returnAddress bytes
    priorLog state segments after :
  Inv_write_output data size returnAddress bytes priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 5 state segments after ->
  exists regs global,
    state.1 = writeSuccess10190Before regs global /\
    after =
      (writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
         returnAddress,
       priorLog ++ writeSuccessWithdrawalsOutputRecordsExact global data size) /\
    writeSuccessOutputRecords data size bytes
      (writeSuccessWithdrawalsOutputRecordsExact global data size).
Proof.
  intros Hinv Hrun.
  destruct (block_write_output_covered data size returnAddress bytes priorLog
    state segments after Hinv Hrun) as
    (regs & global & records & Hentry & Hmachine & Hlog & Hrecords & Houtput).
  subst records. exists regs, global. split; first exact Hentry.
  split; last exact Houtput.
  destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
  subst afterMachine afterLog. reflexivity.
Qed.

Print Assumptions block_write_output_recorded_covered_exact.
