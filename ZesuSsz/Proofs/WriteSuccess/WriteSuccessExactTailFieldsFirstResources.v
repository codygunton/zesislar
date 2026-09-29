Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsCallerJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsTraceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayloadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload158e0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Open Scope Z_scope.

Definition tailFieldsAfterEighthCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  Snapshots.writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv (BV 64 8)
    (ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.writeSuccessPrivateBytes
      (ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.writeSuccessEncodeU64
        (bv_unsigned (writeSuccessPostWord
          (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 6))))
    (writeSuccessExactTailFirstBranchEvents witness).

Definition tailFieldsAfterSeventhCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsByteListsCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostByteLists15950 (writeSuccessPostData witness))
    (tailFieldsAfterEighthCallEvents witness).

Definition tailFieldsAfterSixthCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsByteListsCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostByteLists15940 (writeSuccessPostData witness))
    (tailFieldsAfterSeventhCallEvents witness).

Definition tailFieldsAfterFifthCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsByteListsCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostByteLists15930 (writeSuccessPostData witness))
    (tailFieldsAfterSixthCallEvents witness).

Definition tailFieldsAfterFourthCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsBytesCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostBytes15920 (writeSuccessPostData witness))
    (writeSuccessPostBytes15920Payload (writeSuccessPostData witness))
    (tailFieldsAfterFifthCallEvents witness).

Definition tailFieldsAfterThirdCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsBytesCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostBytes15910 (writeSuccessPostData witness))
    (writeSuccessPostBytes15910Payload (writeSuccessPostData witness))
    (tailFieldsAfterFourthCallEvents witness).

Definition tailFieldsAfterSecondCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsBytesCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostBytes15900 (writeSuccessPostData witness))
    (writeSuccessPostBytes15900Payload (writeSuccessPostData witness))
    (tailFieldsAfterThirdCallEvents witness).

Definition tailFieldsAfterFirstCallEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  tailFieldsBytesCallEvents (writeSuccessFrameSp witness)
    (writeSuccessPostBytes158f0 (writeSuccessPostData witness))
    (writeSuccessPostBytes158f0Payload (writeSuccessPostData witness))
    (tailFieldsAfterSecondCallEvents witness).

Definition tailFieldsPreparedEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (oldS1 : bv 64) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (exactSuffixBytesPayloadEntryRegisters sp (BV 64 0) oldS1 ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$> exactSuffixBytesOtherRegisters) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (tailFieldsFirstSegmentEvents sp (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness) (writeSuccessExactTailFirstBranchEvents witness)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0 /\ mapRamBase defaultMap <= bv_unsigned sp - 80 /\
     bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
   tailFieldsCallerPrepared args witness ∗ True)%I.
Global Instance : LithiumUnfold (@tailFieldsPreparedEntry) := I.

Definition tailFieldsCallerReturn `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (oldS1 ret : bv 64) (descriptor : WriteOutputDescriptor) (tail : spec) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (∃ stack2 : bv 64,
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits descriptor.1 ∗ "x11" ↦ᵣ RVal_Bits descriptor.2 ∗
   encoderBytesExactOutputResources descriptor.2 sp ret (BV 64 0) oldS1 stack2 True ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$> exactSuffixBytesOtherRegisters) ∗
   tailFieldsCallerPrepared args witness ∗
   ⌜bv_unsigned sp `mod` 16 = 0 /\ mapRamBase defaultMap <= bv_unsigned sp - 80 /\
     bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@tailFieldsCallerReturn) := I.
