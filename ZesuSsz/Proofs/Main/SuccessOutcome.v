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
Require Import ZesuSsz.Proofs.Main.SuccessAfterDecode.

Definition mainSuccessOutcomeResources `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation)
 (tail : spec) (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation) :
 IslarisContractResources unit ByteString := {|
 islarisCode :=
  (islarisCode _ _ (mainSuccessAfterDecodeResources allows
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   args observation) ∗ writeSuccessNativeCode ∗
   islarisCode _ _ (mainSuccessFinishResources tail (BV 64 0) (BV 64 0)
    (BV 64 0) (BV 64 0) (BV 64 0) True%I))%I;
 islarisEntry := fun _ => islarisEntry _ _ (mainSuccessAfterDecodeResources allows
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   args observation) tt;
 islarisExit := fun _ bytes =>
  (∃ (witness : writeSuccessNativeWitness WriteSuccessObservation)
    (allocatorPointer allocatorSize a0 a1 a2 x5 x6 : bv 64),
   ⌜writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness⌝ ∗
   ⌜outputRelation (mainWriterArgs args observation) witness bytes⌝ ∗
   islarisExit _ _ (mainSuccessFinishResources tail
    (Z_to_bv 64 (decodeStackPointer args)) a0 a1 x5 x6
    (mainSuccessWriterTerminalFrame args witness allocatorPointer allocatorSize a2)) tt tt)%I
|}.

Theorem main_success_outcome_state_correct `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation)
 (tail : spec) (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation)
 (writeOk : IslarisContractCorrect 0x14d30 0x14d10
   (writeSuccessFixedTailModel writeAllows outputRelation
    (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail) (fun _ nextPc => nextPc = 0x14d10))) :
 allows args (DecodeBoundarySuccess observation) ->
 ⊢ IslarisContractSpec 0x14cfc 0x101d0
  (fun _ bytes => writeAllows (mainWriterArgs args observation) bytes)
  (mainSuccessOutcomeResources allows outputRelation tail args observation).
Proof.
 intros Hallowed.
 rewrite /IslarisContractSpec /mainSuccessOutcomeResources /=.
 iIntros "(HglueCode&HwriterCode&HfinishCode)" (contractArgs).
 iPoseProof (main_success_after_decode_state_correct allows
  (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
  (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
  args observation Hallowed with "HglueCode") as "Hglue".
 iSpecialize ("Hglue" $! tt).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hglue".
 rewrite instr_pre'_eq /instr_pre'_def /=. iIntros "[Hentry Hreturn]".
 iApply "Hglue". iFrame "Hentry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
 iDestruct "Hexit" as (allocatorPointer allocatorSize) "(HwriterEntry&Hcaller&_)".
 iPoseProof (writeOk Sigma _ _) as "Hwriter".
 iEval (rewrite /writeSuccessFixedTailModel /writeSuccessFixedTailResources /=) in "Hwriter".
 iSpecialize ("Hwriter" with "HwriterCode").
 iSpecialize ("Hwriter" $! (mainWriterArgs args observation)).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hwriter".
 iApply "Hwriter". iFrame "HwriterEntry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (bytes) "[%HwriteAllowed Hterminal]".
 iPoseProof (main_success_writer_terminal_entry outputRelation tail args observation
  bytes allocatorPointer allocatorSize with "[Hterminal Hcaller]") as "Hentry".
 { iFrame. }
 iDestruct "Hentry" as (witness a0 a1 a2 x5 x6) "(%Hwell&%Houtput&Hentry)".
 iPoseProof (main_success_finish_state_correct tail
  (Z_to_bv 64 (decodeStackPointer args)) a0 a1 x5 x6
  (mainSuccessWriterTerminalFrame args witness allocatorPointer allocatorSize a2)
  with "HfinishCode") as "Hfinish".
 iSpecialize ("Hfinish" $! tt).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hfinish".
 iApply "Hfinish". iFrame "Hentry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (finishOutcome) "[_ Hterminal]".
 iApply "Hreturn". iExists bytes. iSplit; first done.
 iExists witness, allocatorPointer, allocatorSize, a0, a1, a2, x5, x6. iFrame. done.
Qed.
Print Assumptions main_success_outcome_state_correct.
