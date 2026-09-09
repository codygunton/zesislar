From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Ltac solve_blocker_empty_slice :=
  exists 0%Z; split;
  [change (0 <= 0 < 18446744073709551616)%Z; lia|];
  split; [native_compute; reflexivity|];
  split; native_compute; reflexivity.

Lemma writeSuccessBlockerBlobGasUsed :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 104) 8
    (observationBlobGasUsed writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerExcessBlobGas :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 112) 8
    (observationExcessBlobGas writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerSlotNumber :
  writeSuccessMemoryOptionalU64 writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 120
    (observationSlotNumber writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerBlockAccessList :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 136
    (observationBlockAccessList writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerParentHash :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 152)
    (observationParentHash writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerFeeRecipient :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 184)
    (observationFeeRecipient writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerStateRoot :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 204)
    (observationStateRoot writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerReceiptsRoot :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 236)
    (observationReceiptsRoot writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerLogsBloom :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 268)
    (observationLogsBloom writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerPrevRandao :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 524)
    (observationPrevRandao writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerBlockHash :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 556)
    (observationBlockHash writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Print Assumptions writeSuccessBlockerBlobGasUsed.
Print Assumptions writeSuccessBlockerBlockAccessList.
Print Assumptions writeSuccessBlockerLogsBloom.
