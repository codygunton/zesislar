From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.

Lemma writeSuccessWithdrawals156c0OutputRecorded args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 4
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal)
      segments
      (writeSuccessWithdrawalsOutputEntry
        (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
        (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
        (sp + BV 64 1768)%bv,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as (x11 & x10 & x1 & Hpc & Hx11 & Hx18 & Hx10 & Hx1 & Hm & Htable).
  rewrite (writeSuccessWithdrawalsSecondEncoderEndpointBefore args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2).
  unfold writeSuccessWithdrawalsOutputEntry.
  eapply writeSuccessWithdrawals156c0OutputRecordedDirect; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawals156c0OutputRecorded.
