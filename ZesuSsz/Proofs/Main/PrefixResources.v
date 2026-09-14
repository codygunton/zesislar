Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.DecodeEntry.
Require Import ZesuSsz.Proofs.Main.Prologue.
Require Import ZesuSsz.Proofs.Main.AllocatorAdapter.

Definition mainPrefixInitialSp (args : DecodeBoundaryArgs) : bv 64 :=
  (Z_to_bv 64 (decodeStackPointer args) + BV 64 896)%bv.
Definition mainPrefixReadArgs (args : DecodeBoundaryArgs) : ReadInputArgs := {|
  readReturnAddress := 0x14ccc;
  readBufferSlot := decodeStackPointer args;
  readSizeSlot := decodeStackPointer args + 8;
  readInputBytes := decodeInput args;
  readSavedFrameAddress := decodeStackPointer args + 888;
  readSavedReturnAddress := bv_unsigned (Z_to_bv 64 (decodeSavedReturnAddress args))
|}.
Definition mainPrefixOtherRegisters `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> ["x3"; "x4"]) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x7"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29"; "x30"; "x31"]))%I.
Definition mainPrefixGlobals `{!islaG Sigma} (args : DecodeBoundaryArgs) : iProp Sigma :=
  (⌜decodeInputAddress args = mapInputBufferAddress defaultMap⌝ ∗
   ⌜decodeAllocatorStateAddress args = mainAllocatorStateAddress⌝ ∗
   ⌜decodeAllocatorVtableAddress args = mainAllocatorVtableAddress⌝ ∗
   ⌜(length (decodeInput args) <= maxSszInputSize)%nat⌝ ∗
   mainAllocatorVtableAddress ↦ₘ∗ mainAllocatorVtableBytes ∗
   mainFailurePayloadAddress ↦ₘ∗ failureMemory ∗
   mmio_range (machineExitAddress defaultMap) 8)%I.
Definition mainPrefixCommonFrame `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs) : iProp Sigma :=
  let D := decodeStackPointer args in let sp := Z_to_bv 64 D in
  (⌜decodeReturnAddress args = 0x14cfc⌝ ∗
   ⌜length (decodeSavedRegisters args) = 12%nat⌝ ∗
   ⌜D `mod` 16 = 0⌝ ∗
   ⌜mapRamBase defaultMap + 0x880 <= D⌝ ∗
   ⌜D + 0x7d0 < machineRamEnd defaultMap⌝ ∗
   mainPrefixOtherRegisters ∗
   ([∗ list] register; value ∈
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; decodeSavedRegisters args,
     register ↦ᵣ RVal_Bits (value : bv 64)) ∗
   ⌜length (decodeFramePadding args) = 6%nat⌝ ∗
   (D + 882) ↦ₘ∗ decodeFramePadding args ∗
   (D + 32) ↦ₘ? 848 ∗ (D + 880) ↦ₘ? 2 ∗
   writeSuccessScratch sp ∗ (D - 0x7d0) ↦ₘ? 1896 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (decodeTail args) ∗
   mainDecoderHeapEntry args ∗ mainPrefixGlobals args ∗ True)%I.
Definition mainPrefixFrame `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs)
    (oldInput x5 x6 x12 x13 : bv 64) : iProp Sigma :=
  let D := decodeStackPointer args in
  (mainPrefixCommonFrame decodeTail args ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗ "x13" ↦ᵣ RVal_Bits x13 ∗
   D ↦ₘ oldInput ∗ (D + 16) ↦ₘ? 8 ∗ (D + 24) ↦ₘ? 8 ∗
   (mapInputBufferAddress defaultMap) ↦ₘ∗ readInputMemory (decodeInput args) ∗
   (mapIoContextAddress defaultMap) ↦ₘ
     (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))))%I.
Definition mainPrefixReadFrame `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs)
    (x12 x13 : bv 64) : iProp Sigma :=
  let D := decodeStackPointer args in
  (mainPrefixCommonFrame decodeTail args ∗ "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 D) ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗ "x13" ↦ᵣ RVal_Bits x13 ∗
   (D + 16) ↦ₘ? 8 ∗ (D + 24) ↦ₘ? 8)%I.
Definition mainPrefixAllocatorFrame `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs) : iProp Sigma :=
  let D := decodeStackPointer args in
  (mainPrefixCommonFrame decodeTail args ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
   (D + 888) ↦ₘ (Z_to_bv 64 (decodeSavedReturnAddress args)) ∗
   (mapInputBufferAddress defaultMap) ↦ₘ∗ readInputMemory (decodeInput args) ∗
   (mapIoContextAddress defaultMap) ↦ₘ
     (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))))%I.
Definition mainAllocatorPrefixResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) :
    IslarisContractResources DecodeBoundaryArgs unit := {|
  islarisCode := ([∗ list] i ∈ IslaTraces.allocator_get.instrs.instr_map, instr i.1 (Some i.2))%I;
  islarisEntry := fun args =>
    (mainAllocatorEntry (Z_to_bv 64 (decodeStackPointer args))
       (Z_to_bv 64 (decodeInputAddress args))
       (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
     mainPrefixAllocatorFrame decodeTail args ∗ True)%I;
  islarisExit := fun args _ =>
    islarisEntry _ _
      (mainBeforeDecodeCallResources decodeTail successExitTail (BV 64 0x14ccc)
        (BV 64 mainAllocatorStateAddress) (BV 64 mainAllocatorVtableAddress)) args
|}.
Definition mainPrefixResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
    IslarisContractResources DecodeBoundaryArgs unit := {|
  islarisCode :=
    (([∗ list] i ∈ mainPrologueInstrs, instr i.1 (Some i.2)) ∗
     islarisCode _ _ read_input_resources ∗
     ([∗ list] i ∈ IslaTraces.allocator_get.instrs.instr_map, instr i.1 (Some i.2)))%I;
  islarisEntry := fun args =>
    (mainPrologueEntry (mainPrefixInitialSp args)
      (Z_to_bv 64 (decodeSavedReturnAddress args)) a0 a1 oldSaved oldSize ∗
     mainPrefixFrame decodeTail args oldInput x5 x6 x12 x13 ∗ True)%I;
  islarisExit := fun args _ =>
    islarisEntry _ _
      (mainBeforeDecodeCallResources decodeTail successExitTail (BV 64 0x14ccc)
        (BV 64 mainAllocatorStateAddress) (BV 64 mainAllocatorVtableAddress)) args
|}.
