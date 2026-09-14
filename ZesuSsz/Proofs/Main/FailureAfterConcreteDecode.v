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
Require Import ZesuSsz.Proofs.Main.TerminalFrames.
Require Import ZesuSsz.Proofs.Main.TerminalEntryBridge.

Definition mainFailureAfterConcreteDecodeResources `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (successExitTail : DecodeBoundaryArgs -> spec) (tail : spec) (args : DecodeBoundaryArgs) :
 IslarisContractResources unit unit := {|
 islarisCode := islarisCode _ _ (mainFailureAfterDecodeResources tail
  (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14cfc) (BV 16 1) True%I);
 islarisEntry := fun _ => islarisExit _ _ (mainDecodeConcreteResources
  (mainDecodeUnionTail allows successExitTail
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
  successExitTail) args DecodeBoundaryFailure;
 islarisExit := fun _ _ =>
  (∃ (status : bv 16) (allocatorPointer allocatorSize a2 : bv 64) (objectBytes : list (bv 8)),
   ⌜status <> BV 16 0⌝ ∗ ⌜length objectBytes = 848%nat⌝ ∗
   islarisExit _ _ (mainFailureAfterDecodeResources tail
    (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14cfc) status
    (mainFailureDecoderFrame args allocatorPointer allocatorSize a2 objectBytes)) tt tt)%I
|}.

Theorem main_failure_after_concrete_decode_state_correct `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (successExitTail : DecodeBoundaryArgs -> spec) (tail : spec) (args : DecodeBoundaryArgs) :
 allows args DecodeBoundaryFailure ->
 ⊢ IslarisContractSpec 0x14cfc 0x101d0 (fun _ _ => True%type)
  (mainFailureAfterConcreteDecodeResources allows successExitTail tail args).
Proof.
 intros Hallowed.
 rewrite /IslarisContractSpec /mainFailureAfterConcreteDecodeResources /=.
 iIntros "Hcode" (contractArgs).
 rewrite instr_pre'_eq /instr_pre'_def /=. iIntros "[Hentry Hreturn]".
 iPoseProof (main_failure_concrete_entry allows successExitTail tail args Hallowed
  with "Hentry") as "Hentry".
 iDestruct "Hentry" as (status allocatorPointer allocatorSize a2 objectBytes)
  "(%Hstatus&%Hlength&Hentry)".
 iPoseProof (main_failure_after_decode_state_correct tail
  (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14cfc) status
  (mainFailureDecoderFrame args allocatorPointer allocatorSize a2 objectBytes)
  with "Hcode") as "Hnative".
 iSpecialize ("Hnative" $! tt).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
 iApply "Hnative". iFrame "Hentry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
 iApply "Hreturn". iExists tt. iSplit; first done.
 iExists status, allocatorPointer, allocatorSize, a2, objectBytes. iFrame. done.
Qed.
Print Assumptions main_failure_after_concrete_decode_state_correct.
