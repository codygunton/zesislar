From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.

Lemma writeSuccessBlockerAllBytesRead :
  read_mem_list writeSuccessBlockerRepresentedMemory 0x20001000 96%N =
    Some writeSuccessBlockerAllBytes.
Proof.
  unfold writeSuccessBlockerRepresentedMemory.
  apply read_mem_list_written.
  unfold islaMemoryRange, writeSuccessBlockerAllBytes,
    writeSuccessBlockerCurrent, writeSuccessBlockerNext.
  cbn. lia.
Qed.

Lemma writeSuccessBlockerCurrentRead :
  read_mem_list writeSuccessBlockerRepresentedMemory 0x20001000 48%N =
    Some writeSuccessBlockerCurrent.
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerScratchRead :
  read_mem_list writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerScratch 48%N =
    Some writeSuccessBlockerScratchBefore.
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerEncoderScratchRead :
  read_mem_list writeSuccessBlockerRepresentedMemory 0x20000ff0 16%N =
    Some writeSuccessBlockerEncoderScratch.
Proof. native_compute; reflexivity. Qed.

Print Assumptions writeSuccessBlockerAllBytesRead.
Print Assumptions writeSuccessBlockerCurrentRead.
Print Assumptions writeSuccessBlockerScratchRead.
Print Assumptions writeSuccessBlockerEncoderScratchRead.
