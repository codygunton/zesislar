From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Definition writeSuccessBlockerTopBytes : list (bv 8) :=
  match read_mem_list writeSuccessBlockerRepresentedMemory
      writeSuccessBlockerOwner 848%N with
  | Some bytes => bytes
  | None => []
  end.

Lemma writeSuccessBlockerTop :
  exists top, length top = 848%nat /\
    read_mem_list writeSuccessBlockerRepresentedMemory
      writeSuccessBlockerOwner 848%N = Some top.
Proof.
  exists writeSuccessBlockerTopBytes. split;
    unfold writeSuccessBlockerTopBytes; native_compute.
  all: try reflexivity.
Qed.

Lemma writeSuccessBlockerBlockNumber :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 8
    (observationBlockNumber writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerGasLimit :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 8) 8
    (observationGasLimit writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerGasUsed :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 16) 8
    (observationGasUsed writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerTimestamp :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 24) 8
    (observationTimestamp writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerExtraData :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 32
    (observationExtraData writeSuccessBlockerDecoded).
Proof.
  exists writeSuccessBlockerScratch. split.
  - change (0 <= 536876752 < 18446744073709551616)%Z; lia.
  - split.
    + native_compute; reflexivity.
    + split; native_compute; reflexivity.
Qed.

Lemma writeSuccessBlockerBaseFee :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 48) 8
    (observationBaseFee writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Print Assumptions writeSuccessBlockerTop.
Print Assumptions writeSuccessBlockerExtraData.
Print Assumptions writeSuccessBlockerBaseFee.
