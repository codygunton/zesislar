From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.

Lemma writeSuccessWithdrawals156a8CoverageLast regs global sp pointer current
    withdrawal segments after :
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess15694Mstatus = Some (Val_Bool true) ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  IslaInstructionRun 1 (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal) segments after ->
  segments = [writeSuccess156b0Observations
    (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs)
    (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).2] /\
  after = writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal.
Proof.
  intros Hma Hcode Hnext Hrun.
  inversion Hrun as [|? ? obs middle tail machineAfter Hseg Htail]; subst.
  have Hpc := writeSuccessWithdrawals156b0Pc regs global sp pointer current withdrawal.
  have Hx1 := writeSuccessWithdrawals156b0X1 regs global sp pointer current withdrawal.
  have Hma2 := writeSuccessWithdrawals156b0Mstatus regs global sp pointer current withdrawal Hma.
  destruct (segment_156b0_mstatus_covered _ _ obs middle Hpc Hx1 Hcode Hnext Hma2 Hseg) as (-> & ->).
  inversion Htail; subst. split; reflexivity.
Qed.
Print Assumptions writeSuccessWithdrawals156a8CoverageLast.
