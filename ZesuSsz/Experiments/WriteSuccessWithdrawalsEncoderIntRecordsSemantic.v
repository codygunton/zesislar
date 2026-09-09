From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderIntRecordsSemantic global sp returnAddress
    value :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
    (bv_to_little_endian 8 8 (bv_unsigned value))
    (writeSuccessWithdrawalsEncoderIntRecords global sp returnAddress value).
Proof.
  intros Hrange.
  have Hread := writeSuccessEncoderIntAfterStoresValue global sp returnAddress
    value Hrange.
  unfold writeSuccessOutputRecords,
    writeSuccessWithdrawalsEncoderIntRecords.
  split; first reflexivity.
  unfold writeSuccessWithdrawalsRecordedPayloads.
  rewrite bool_decide_true.
  2: { split; bv_solve. }
  change (match read_mem_list
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
      (bv_unsigned (sp - BV 64 16)%bv) 8%N,
      Some [] with
    | Some payload, Some payloads => Some (payload :: payloads)
    | _, _ => None
    end = Some [bv_to_little_endian 8 8 (bv_unsigned value)]).
  rewrite writeSuccessEncoderIntStackUnsigned; last exact Hrange.
  rewrite Hread.
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntRecordsSemantic.
