Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.

Definition mainAllocatorStateAddress : Z :=
  (mapIoContextAddress defaultMap - 8)%Z.
Definition mainAllocatorVtableAddress : Z :=
  (mapRodataBase defaultMap + 0x5a8)%Z.
Definition mainFailurePayloadAddress : Z :=
  (mapRodataBase defaultMap + 0x5c8)%Z.

Definition mainAllocatorVtableBytes : list (bv 8) :=
  bv_to_little_endian 8 8 (machinePc 0x5edc) ++
  bv_to_little_endian 8 8 (machinePc 0x5c20) ++
  bv_to_little_endian 8 8 (machinePc 0x5c18) ++
  bv_to_little_endian 8 8 (machinePc 0x58f4).

Definition mainDecoderLowerScratch `{!islaG Sigma}
    (args : DecodeBoundaryArgs) : iProp Sigma :=
  ((decodeStackPointer args - 2048) ↦ₘ? 48 ∗
   (decodeStackPointer args - 2080) ↦ₘ? 32)%I.

Definition mainDecoderHeapEntry `{!islaG Sigma}
    (args : DecodeBoundaryArgs) : iProp Sigma :=
  ((mapHeapBase defaultMap) ↦ₘ?
     (mapHeapEnd defaultMap - mapHeapBase defaultMap) ∗
   mainAllocatorStateAddress ↦ₘ (BV 64 0) ∗
   (mapHeapTopAddress defaultMap) ↦ₘ (BV 64 (mapHeapEnd defaultMap)) ∗
   (mapHeapPosAddress defaultMap) ↦ₘ (BV 64 (mapHeapBase defaultMap)) ∗
   mainDecoderLowerScratch args ∗ writeSuccessNativeStaticResources)%I.

Definition mainDecoderHeapFailureExit `{!islaG Sigma}
    (args : DecodeBoundaryArgs) : iProp Sigma :=
  (∃ allocatorState heapTop heapPos : bv 64,
   (mapHeapBase defaultMap) ↦ₘ?
     (mapHeapEnd defaultMap - mapHeapBase defaultMap) ∗
   mainAllocatorStateAddress ↦ₘ allocatorState ∗
   (mapHeapTopAddress defaultMap) ↦ₘ heapTop ∗
   (mapHeapPosAddress defaultMap) ↦ₘ heapPos ∗
   mainDecoderLowerScratch args ∗ writeSuccessNativeStaticResources)%I.

Definition mainDecoderPreservedFrame `{!islaG Sigma}
    (args : DecodeBoundaryArgs) : iProp Sigma :=
  (⌜decodeInputAddress args = mapInputBufferAddress defaultMap⌝ ∗
   ⌜decodeAllocatorStateAddress args = mainAllocatorStateAddress⌝ ∗
   ⌜decodeAllocatorVtableAddress args = mainAllocatorVtableAddress⌝ ∗
   ⌜(length (decodeInput args) <= maxSszInputSize)%nat⌝ ∗
   (mapInputBufferAddress defaultMap) ↦ₘ∗ readInputMemory (decodeInput args) ∗
   (mapIoContextAddress defaultMap) ↦ₘ
     (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
   mainAllocatorVtableAddress ↦ₘ∗ mainAllocatorVtableBytes ∗
   mainFailurePayloadAddress ↦ₘ∗ failureMemory ∗
   mmio_range (machineExitAddress defaultMap) 8)%I.

(** The decoder hypothesis uses this concrete physical handoff. *)
Definition mainDecodeConcreteResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) :=
  mainDecodeMachineResources decodeTail successExitTail
    mainDecoderPreservedFrame mainDecoderHeapEntry mainDecoderHeapFailureExit.
