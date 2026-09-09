From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefixMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefixMemcpyRecordedJoin args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments regs global,
    WriteSuccessWithdrawalsRecordedRun 344 state segments
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global.
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsPrefixMemcpyRecorded args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (segments & after & regs & global & returnTrace & Hrun & Hentry & Hreturn &
     Hafter & Hpc & Hdestination & Hsource & Hframe & Hlog).
  have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  rewrite Hentry in Hmemcpy.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_memcpy in Hmemcpy; cbn in Hmemcpy; tauto).
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8.
  { apply Htable. cbn. tauto. }
  rewrite Hreturn in Hcode. inversion Hcode. subst returnTrace.
  exists segments, regs, global. split; last exact Hentry.
  destruct after as [afterMachine afterLog]. cbn in Hafter, Hlog, Hrun |- *.
  subst afterMachine afterLog.
  unfold writeSuccessWithdrawals156a8State,
    writeSuccessWithdrawals156a8Regs, writeSuccessWithdrawals156a8Global.
  exact Hrun.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixMemcpyRecordedJoin.
