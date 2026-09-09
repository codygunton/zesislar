From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4Existence.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefixMemcpyEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefixMemcpyExistence.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefixMemcpyRecorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments after regs global returnTrace,
    WriteSuccessWithdrawalsRecordedRun 344 state segments after /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some returnTrace /\
    after.1 =
      (writeSuccess15694Local returnTrace
        (writeSuccessMemcpyEndpointRegs regs global pointer
          (sp + BV 64 1744)%bv current (Z_to_bv 64 0x156a8)),
       writeSuccessMemcpyEndpointGlobal regs global pointer
         (sp + BV 64 1744)%bv current) /\
    writeSuccessWithdrawalsConcretePc after = Some 0x156a8 /\
    read_mem_list after.1.2.(seq_mem) (bv_unsigned (sp + BV 64 1744)%bv)
      (N.of_nat (length current)) = Some current /\
    read_mem_list after.1.2.(seq_mem) (bv_unsigned pointer)
      (N.of_nat (length current)) = Some current /\
    writeSuccessMemoryRangeFrame (bv_unsigned (sp + BV 64 1744)%bv)
      (length current) after.1.2.(seq_mem) state.1.2.(seq_mem) /\
    after.2 = priorLog.
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsPrefixMemcpyExists args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (prefixSegments & memcpySegments & after & Hprefix & Hmemcpy & Hall & Hpc &
     Hdestination & Hsource & Hframe & Hlog).
  destruct (writeSuccessWithdrawalsPrefixMemcpyEndpoint args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state memcpySegments after
    Hinv Hmemcpy) as (regs & global & returnTrace & Hentry & Hreturn & Hafter).
  exists (prefixSegments ++ memcpySegments), after, regs, global, returnTrace.
  split; first exact Hall.
  split; first exact Hentry.
  split; first exact Hreturn.
  split; first exact Hafter.
  split; first exact Hpc.
  split; first exact Hdestination.
  split; first exact Hsource.
  split; first exact Hframe.
  exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixMemcpyRecorded.
