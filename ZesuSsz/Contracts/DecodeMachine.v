Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.

(** The arguments fix the callee-saved values before the decoder call. *)
Definition mainDecoderRegisters `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (saved : list (bv 64)) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x14cfc) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   ([∗ list] register; value ∈
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; saved,
      register ↦ᵣ RVal_Bits (value : bv 64)) ∗
   (∃ a0 a1 a2 : bv 64,
      "x10" ↦ᵣ RVal_Bits a0 ∗ "x11" ↦ᵣ RVal_Bits a1 ∗
      "x12" ↦ᵣ RVal_Bits a2))%I.

Definition mainDecoderCallerFrame `{!islaG Sigma}
    (sp inputPointer inputSize allocatorPointer allocatorSize savedRa : bv 64)
    (padding : list (bv 8)) : iProp Sigma :=
  (⌜length padding = 6%nat⌝ ∗
   bv_unsigned sp ↦ₘ inputPointer ∗
   (bv_unsigned sp + 8) ↦ₘ inputSize ∗
   (bv_unsigned sp + 16) ↦ₘ allocatorPointer ∗
   (bv_unsigned sp + 24) ↦ₘ allocatorSize ∗
   (bv_unsigned sp + 882) ↦ₘ∗ padding ∗
   (bv_unsigned sp + 888) ↦ₘ savedRa)%I.


Definition mainDecoderObjectResources `{!islaG Sigma} `{!threadG}
    (args : DecodeBoundaryArgs) (saved : list (bv 64))
    (successExitTail : DecodeBoundaryArgs -> spec)
    (outcome : DecodeBoundaryOutcome WriteSuccessObservation) : iProp Sigma :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  match outcome with
  | DecodeBoundarySuccess observation =>
      ∃ witness : writeSuccessNativeWitness WriteSuccessObservation,
      let writeArgs := {| successReturnAddress := 0x14d10;
        successStackPointer := decodeStackPointer args;
        successDecodedAddress := decodeStackPointer args + 32;
        successDecoded := observation;
        successInputSize := length (decodeInput args) |} in
      ⌜writeSuccessWitnessWellFormed writeArgs witness⌝ ∗
      ⌜writeSuccessTraceTail witness = successExitTail args⌝ ∗
      ⌜saved = [writeSuccessSavedS0 witness; writeSuccessSavedS1 witness;
        writeSuccessSavedS2 witness; writeSuccessSavedS3 witness;
        writeSuccessSavedS4 witness; writeSuccessSavedS5 witness;
        writeSuccessSavedS6 witness; writeSuccessSavedS7 witness;
        writeSuccessSavedS8 witness; writeSuccessSavedS9 witness;
        writeSuccessSavedS10 witness; writeSuccessSavedS11 witness]⌝ ∗
      (decodeStackPointer args + 880) ↦ₘ (BV 16 0) ∗
      bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
        writeSuccessDecodedBytes witness ∗
      writeSuccessNativeDataResources witness
  | DecodeBoundaryFailure =>
      ∃ (status : bv 16) (objectBytes : list (bv 8)),
      ⌜status <> BV 16 0⌝ ∗ ⌜length objectBytes = 848%nat⌝ ∗
      (decodeStackPointer args + 880) ↦ₘ status ∗
      (decodeStackPointer args + 32) ↦ₘ∗ objectBytes
  end.

(* Root supplies concrete allocation resources. These parameters do not add proof hypotheses. *)
Definition mainDecodeMachineResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (preservedFrame decoderHeapEntry : DecodeBoundaryArgs -> iProp Sigma)
    (decoderHeapFailureExit : DecodeBoundaryArgs -> iProp Sigma) :
    IslarisContractResources DecodeBoundaryArgs
      (DecodeBoundaryOutcome WriteSuccessObservation) := {|
  islarisCode := True%I;
  islarisEntry := fun args =>
    (let sp := Z_to_bv 64 (decodeStackPointer args) in
     ⌜decodeReturnAddress args = 0x14cfc⌝ ∗
     ⌜length (decodeSavedRegisters args) = 12%nat⌝ ∗
     ⌜decodeStackPointer args `mod` 16 = 0⌝ ∗
     ⌜(mapRamBase defaultMap + 0x880) <= decodeStackPointer args⌝ ∗
     ⌜decodeStackPointer args + 0x7d0 < (machineRamEnd defaultMap)⌝ ∗
     reg_col zesu_sys_regs ∗
     reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
       List.filter (fun register => negb (String.eqb register "x13")) writeSuccessOtherRegisters) ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x14cfc) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     ([∗ list] register; value ∈
       ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
        "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; decodeSavedRegisters args,
       register ↦ᵣ RVal_Bits (value : bv 64)) ∗
     "x10" ↦ᵣ RVal_Bits (sp + BV 64 32)%bv ∗
     "x11" ↦ᵣ RVal_Bits (sp + BV 64 16)%bv ∗
     "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeInputAddress args)) ∗
     "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
     mainDecoderCallerFrame sp (Z_to_bv 64 (decodeInputAddress args))
       (Z_to_bv 64 (Z.of_nat (length (decodeInput args))))
       (Z_to_bv 64 (decodeAllocatorStateAddress args))
       (Z_to_bv 64 (decodeAllocatorVtableAddress args))
       (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
     (decodeStackPointer args + 32) ↦ₘ? 848 ∗
     (decodeStackPointer args + 880) ↦ₘ? 2 ∗
     writeSuccessScratch sp ∗
     (decodeStackPointer args - 0x7d0) ↦ₘ? 1896 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (decodeTail args) ∗
     decoderHeapEntry args ∗ preservedFrame args)%I;
  islarisExit := fun args outcome =>
    (let sp := Z_to_bv 64 (decodeStackPointer args) in
     ∃ allocatorPointer allocatorSize : bv 64,
     mainDecoderRegisters sp (decodeSavedRegisters args) ∗
     mainDecoderCallerFrame sp (Z_to_bv 64 (decodeInputAddress args))
       (Z_to_bv 64 (Z.of_nat (length (decodeInput args))))
       allocatorPointer allocatorSize
       (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
     ⌜length (decodeSavedRegisters args) = 12%nat⌝ ∗
     ⌜decodeStackPointer args `mod` 16 = 0⌝ ∗
     ⌜(mapRamBase defaultMap + 0x880) <= decodeStackPointer args⌝ ∗
     ⌜decodeStackPointer args + 0x7d0 < (machineRamEnd defaultMap)⌝ ∗
     ⌜bv_unsigned sp = decodeStackPointer args⌝ ∗
     ⌜(bv_unsigned ((sp + BV 64 32)%bv) = decodeStackPointer args + 32)%Z⌝ ∗
     mainDecoderObjectResources args (decodeSavedRegisters args) successExitTail outcome ∗
     (match outcome with
      | DecodeBoundarySuccess _ => True
      | DecodeBoundaryFailure => decoderHeapFailureExit args
      end) ∗
     writeSuccessScratch sp ∗
     (decodeStackPointer args - 0x7d0) ↦ₘ? 1896 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (decodeTail args) ∗
     preservedFrame args)%I
|}.
