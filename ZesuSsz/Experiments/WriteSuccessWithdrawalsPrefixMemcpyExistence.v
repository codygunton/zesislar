From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefixMemcpyExists args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists prefixSegments memcpySegments after,
    WriteSuccessWithdrawalsRecordedRun 5 state prefixSegments
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 339
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
      memcpySegments after /\
    WriteSuccessWithdrawalsRecordedRun 344 state
      (prefixSegments ++ memcpySegments) after /\
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
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HprefixInv := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  destruct (writeSuccessWithdrawalsPrefix15694Recorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (prefixSegments & HprefixRun).
  set (middle :=
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)).
  change (Inv_memcpy (sp + BV 64 1744)%bv pointer (Z_to_bv 64 0x156a8)
    current scratch state.1.2.(seq_mem) priorLog middle) in HprefixInv.
  destruct (block_memcpy_recorded (sp + BV 64 1744)%bv pointer
    (Z_to_bv 64 0x156a8) current scratch state.1.2.(seq_mem) priorLog middle
    HprefixInv) as (memcpySegments & after & HmemcpyRun & Hpc & Hdestination &
      Hsource & Hframe & Hlog).
  have Hmemcpy339 : WriteSuccessWithdrawalsRecordedRun 339 middle
      memcpySegments after.
  { rewrite Hcurrent in HmemcpyRun. exact HmemcpyRun. }
  have Hall : WriteSuccessWithdrawalsRecordedRun 344 state
      (prefixSegments ++ memcpySegments) after.
  { replace 344%nat with (5 + 339)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  exists prefixSegments, memcpySegments, after.
  split; first exact HprefixRun.
  split; first exact Hmemcpy339.
  split; first exact Hall.
  split.
  - rewrite Hpc. cbn. rewrite Z_to_bv_unsigned. reflexivity.
  - split; first exact Hdestination.
    split; first exact Hsource.
    split; first exact Hframe.
    exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixMemcpyExists.
