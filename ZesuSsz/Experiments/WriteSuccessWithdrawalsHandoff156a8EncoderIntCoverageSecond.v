From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156acCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.

Lemma writeSuccessWithdrawals156a8CoverageSecond regs global sp pointer current
    withdrawal (oldX1 : valu) segments after :
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x1" = Some oldX1 ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess15694Mstatus = Some (Val_Bool true) ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  IslaInstructionRun 2 (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal) segments after ->
  exists observations tail,
    segments = observations :: tail /\
    observations = writeSuccess156acObservations
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).1.(seq_regs)
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).2 /\
    IslaInstructionRun 1 (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal) tail after.
Proof.
  intros Hx1 Hma Hcode Hnext Hrun.
  inversion Hrun as [|? ? obs middle tail machineAfter Hseg Htail]; subst.
  have Hpc1 := writeSuccessWithdrawals156acPc regs global sp pointer current withdrawal.
  have Hx1_1 := writeSuccessWithdrawals156acX1 regs global sp pointer current withdrawal oldX1 Hx1.
  have Hma1 := writeSuccessWithdrawals156acMstatus regs global sp pointer current withdrawal Hma.
  destruct (segment_156ac_mstatus_covered _ _ oldX1 obs middle Hpc1 Hx1_1
    Hcode Hnext Hma1 Hseg) as (-> & ->).
  eexists _, tail. repeat split; assumption || reflexivity.
Qed.
Print Assumptions writeSuccessWithdrawals156a8CoverageSecond.
