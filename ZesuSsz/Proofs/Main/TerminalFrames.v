Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.ReturnedRegisters.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.SuccessFinish.
Require Import ZesuSsz.Proofs.Main.FailureAfterDecode.
Require Import ZesuSsz.Proofs.Main.FailureOutcome.
Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.

Definition mainSuccessReturnedCallerFrame `{!islaG Sigma} `{!threadG}
 (args : DecodeBoundaryArgs) (allocatorPointer allocatorSize : bv 64) : iProp Sigma :=
 (mainDecoderCallerFrame (Z_to_bv 64 (decodeStackPointer args))
   (Z_to_bv 64 (decodeInputAddress args))
   (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) allocatorPointer allocatorSize
   (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
  (decodeStackPointer args + 880) ↦ₘ (BV 16 0) ∗
  mainDecoderPreservedMemoryFrame args)%I.
Definition mainSuccessWriterTerminalFrame `{!islaG Sigma} `{!threadG}
 (args : DecodeBoundaryArgs) (witness : writeSuccessNativeWitness WriteSuccessObservation)
 (allocatorPointer allocatorSize a2 : bv 64) : iProp Sigma :=
 (mainReturnedOtherRegisters ∗
  "x8" ↦ᵣ RVal_Bits (writeSuccessSavedS0 witness) ∗
  "x9" ↦ᵣ RVal_Bits (writeSuccessSavedS1 witness) ∗
  "x18" ↦ᵣ RVal_Bits (writeSuccessSavedS2 witness) ∗
  "x19" ↦ᵣ RVal_Bits (writeSuccessSavedS3 witness) ∗
  "x20" ↦ᵣ RVal_Bits (writeSuccessSavedS4 witness) ∗
  "x21" ↦ᵣ RVal_Bits (writeSuccessSavedS5 witness) ∗
  "x22" ↦ᵣ RVal_Bits (writeSuccessSavedS6 witness) ∗
  "x23" ↦ᵣ RVal_Bits (writeSuccessSavedS7 witness) ∗
  "x24" ↦ᵣ RVal_Bits (writeSuccessSavedS8 witness) ∗
  "x25" ↦ᵣ RVal_Bits (writeSuccessSavedS9 witness) ∗
  "x26" ↦ᵣ RVal_Bits (writeSuccessSavedS10 witness) ∗
  "x27" ↦ᵣ RVal_Bits (writeSuccessSavedS11 witness) ∗
  "x12" ↦ᵣ RVal_Bits a2 ∗ writeSuccessTerminalSavedSlots witness ∗
  writeSuccessNativeExitMemory witness ∗
  mainSuccessReturnedCallerFrame args allocatorPointer allocatorSize ∗ True)%I.

Definition mainFailureDecoderFrame `{!islaG Sigma} `{!threadG}
 (args : DecodeBoundaryArgs) (allocatorPointer allocatorSize a2 : bv 64)
 (objectBytes : list (bv 8)) : iProp Sigma :=
 (mainReturnedOtherRegisters ∗
  ([∗ list] register; value ∈
   ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
    "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; decodeSavedRegisters args,
   register ↦ᵣ RVal_Bits (value : bv 64)) ∗
  "x12" ↦ᵣ RVal_Bits a2 ∗
  mainDecoderCallerFrame (Z_to_bv 64 (decodeStackPointer args))
   (Z_to_bv 64 (decodeInputAddress args))
   (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) allocatorPointer allocatorSize
   (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
  (decodeStackPointer args + 32) ↦ₘ∗ objectBytes ∗
  mainDecoderHeapFailureExit args ∗
  writeSuccessScratch (Z_to_bv 64 (decodeStackPointer args)) ∗
  (decodeStackPointer args - 0x7d0) ↦ₘ? 1896 ∗
  mainDecoderPreservedInputFrame args ∗ True)%I.
