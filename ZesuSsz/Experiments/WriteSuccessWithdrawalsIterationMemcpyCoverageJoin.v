From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockMemcpyCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsIterationMemcpyRecordedCoveredJoin args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 339
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
    segments after ->
  exists regs global,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    after =
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog).
Proof.
  intros Hinv Hrun.
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  set (middle :=
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)).
  change (Inv_memcpy (sp + BV 64 1744)%bv pointer (Z_to_bv 64 0x156a8)
    current scratch state.1.2.(seq_mem) priorLog middle) in Hmemcpy.
  have Hrun' : WriteSuccessWithdrawalsRecordedRun (7 * length current + 3)
      middle segments after.
  { rewrite Hcurrent. exact Hrun. }
  destruct (block_memcpy_recorded_covered (sp + BV 64 1744)%bv pointer
    (Z_to_bv 64 0x156a8) current scratch state.1.2.(seq_mem) priorLog middle
    segments after Hmemcpy Hrun') as
    (Hpc & Hdestination & Hsource & Hframe & Hlog & regs & global &
     returnTrace & Hentry & Hreturn & Hafter).
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_memcpy in Hmemcpy; rewrite Hentry in Hmemcpy; cbn in Hmemcpy;
      tauto).
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8.
  { apply Htable. cbn. tauto. }
  rewrite Hreturn in Hcode. inversion Hcode. subst returnTrace.
  exists regs, global. split; first exact Hentry.
  destruct after as [afterMachine afterLog]. cbn in Hafter, Hlog |- *.
  subst afterMachine afterLog.
  unfold writeSuccessWithdrawals156a8State,
    writeSuccessWithdrawals156a8Regs, writeSuccessWithdrawals156a8Global.
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationMemcpyRecordedCoveredJoin.
