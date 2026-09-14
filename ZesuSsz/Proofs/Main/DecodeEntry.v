Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.Main.DecodeCall.

Definition mainBeforeDecodeCallFrame `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs) : iProp Sigma :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  (⌜decodeReturnAddress args = 0x14cfc⌝ ∗
   ⌜length (decodeSavedRegisters args) = 12%nat⌝ ∗
   ⌜decodeStackPointer args `mod` 16 = 0⌝ ∗
   ⌜mapRamBase defaultMap + 0x880 <= decodeStackPointer args⌝ ∗
   ⌜decodeStackPointer args + 0x7d0 < machineRamEnd defaultMap⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     List.filter (fun register => negb (String.eqb register "x13")) writeSuccessOtherRegisters) ∗
   ([∗ list] register; value ∈
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; decodeSavedRegisters args,
     register ↦ᵣ RVal_Bits (value : bv 64)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeInputAddress args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
   mainDecoderCallerFrame sp (Z_to_bv 64 (decodeInputAddress args))
     (Z_to_bv 64 (Z.of_nat (length (decodeInput args))))
     (Z_to_bv 64 (decodeAllocatorStateAddress args))
     (Z_to_bv 64 (decodeAllocatorVtableAddress args))
     (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
   (decodeStackPointer args + 32) ↦ₘ? 848 ∗
   (decodeStackPointer args + 880) ↦ₘ? 2 ∗
   writeSuccessScratch sp ∗ (decodeStackPointer args - 0x7d0) ↦ₘ? 1896 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (decodeTail args) ∗
   mainDecoderHeapEntry args ∗ mainDecoderPreservedFrame args ∗ True)%I.
Global Instance : LithiumUnfold (@mainBeforeDecodeCallFrame) := I.
Definition mainBeforeDecodeCallResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) (ra a0 a1 : bv 64) :
    IslarisContractResources DecodeBoundaryArgs unit := {|
  islarisCode := ([∗ list] i ∈ mainDecodeCallInstrs, instr i.1 (Some i.2))%I;
  islarisEntry := fun args =>
    (mainCallRegisters (Z_to_bv 64 (decodeStackPointer args)) ra a0 a1 ∗
     mainBeforeDecodeCallFrame decodeTail args ∗ True)%I;
  islarisExit := fun args _ =>
    islarisEntry _ _ (mainDecodeConcreteResources decodeTail successExitTail) args
|}.

Theorem main_before_decode_call_state_correct `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) (ra a0 a1 : bv 64) :
  ⊢ IslarisContractSpec 0x14cec 0x12168 (fun _ _ => True%type)
    (mainBeforeDecodeCallResources decodeTail successExitTail ra a0 a1).
Proof.
  rewrite /IslarisContractSpec /mainBeforeDecodeCallResources
    /mainBeforeDecodeCallFrame /mainDecodeConcreteResources /mainDecodeMachineResources
    /mainCallRegisters /mainDecodeCallInstrs /=.
  zesu_block.
Qed.
Print Assumptions main_before_decode_call_state_correct.
