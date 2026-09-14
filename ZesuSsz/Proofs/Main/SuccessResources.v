Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Definition mainSuccessCallerFrame `{!islaG Sigma} `{!threadG}
    (args : DecodeBoundaryArgs) (allocatorPointer allocatorSize : bv 64) : iProp Sigma :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  (mainDecoderCallerFrame sp (Z_to_bv 64 (decodeInputAddress args))
    (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) allocatorPointer allocatorSize
    (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
   (decodeStackPointer args + 880) ↦ₘ (BV 16 0) ∗
   mainDecoderPreservedFrame args ∗ True)%I.

Definition mainSuccessAfterDecodeResources `{!islaG Sigma} `{!threadG}
    (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
    (successExitTail failureExitTail : DecodeBoundaryArgs -> spec)
    (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation) :
    IslarisContractResources unit unit := {|
  islarisCode := (([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) ∗
    ([∗ list] i ∈ main_write_success_instrs, instr i.1 (Some i.2)))%I;
  islarisEntry := fun _ => islarisExit _ _
    (mainDecodeConcreteResources (mainDecodeUnionTail allows successExitTail failureExitTail)
      successExitTail) args (DecodeBoundarySuccess observation);
  islarisExit := fun _ _ =>
    (∃ allocatorPointer allocatorSize : bv 64,
      writeSuccessFixedTailEntry (successExitTail args) (mainWriterArgs args observation) ∗
      mainSuccessCallerFrame args allocatorPointer allocatorSize ∗ True)%I
|}.
