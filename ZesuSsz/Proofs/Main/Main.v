Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.PrefixToDecodeEntry.
Require Import ZesuSsz.Proofs.Main.SuccessOutcome.
Require Import ZesuSsz.Proofs.Main.FailureAfterConcreteDecode.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.SuccessFinish.
Require Import ZesuSsz.Proofs.Main.FailureAfterDecode.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.ZkvmExit.TraceContract.

Require Import ZesuSsz.Proofs.Main.WholeResources.
Require Import ZesuSsz.Proofs.Main.WholeCode.

Local Opaque writeSuccessNativeCode.

Theorem main_whole_state_correct `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation) (tail : spec)
 (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64)
 (decodeOk : IslarisContractCorrect 0x12168 0x14cfc
  (mainConcreteDecodeModel allows
   (mainDecodeUnionTail allows
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)))
 (writeOk : IslarisContractCorrect 0x14d30 0x14d10
  (writeSuccessFixedTailModel writeAllows outputRelation
   (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   (fun _ nextPc => nextPc = 0x14d10))) :
 ⊢ IslarisContractSpec 0x14cb0 0x101d0 (mainWholeAllows allows writeAllows)
  (mainWholeResources allows outputRelation tail a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13).
Proof.
 rewrite /IslarisContractSpec /mainWholeResources /=.
 iIntros "(HprefixCode&HsuccessCode&HfailureCode)" (args).
 iPoseProof (main_to_decode_entry_state_correct
  (mainDecodeUnionTail allows
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
  (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
  a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 with "HprefixCode") as "Hprefix".
 iSpecialize ("Hprefix" $! args).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hprefix".
 rewrite instr_pre'_eq /instr_pre'_def /=. iIntros "[Hentry Hreturn]".
 iApply "Hprefix". iFrame "Hentry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (prefixOutcome) "[_ Hentry]".
 iPoseProof (decodeOk Sigma _ _) as "Hdecode".
 iEval (rewrite /mainConcreteDecodeModel /=) in "Hdecode".
 iSpecialize ("Hdecode" with "[]"); first done.
 iSpecialize ("Hdecode" $! args).
 iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hdecode".
 iApply "Hdecode". iFrame "Hentry".
 iNext. iIntros "Hexit". iDestruct "Hexit" as (decodeOutcome) "[%Hallowed Hentry]".
 destruct decodeOutcome as [|observation].
 - iPoseProof (main_failure_after_concrete_decode_state_correct allows
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    tail args Hallowed with "HfailureCode") as "Hfailure".
   iSpecialize ("Hfailure" $! tt).
   iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hfailure".
   iApply "Hfailure". iFrame "Hentry".
   iNext. iIntros "Hexit". iDestruct "Hexit" as (failureOutcome) "[_ Hterminal]".
   iApply "Hreturn". iExists (DecodeBoundaryFailure, failureObservation).
   rewrite /mainWholeAllows /=. iSplit; first done. iFrame. done.
 - iEval (rewrite (main_success_outcome_code allows outputRelation tail args observation)) in "HsuccessCode".
   iPoseProof (main_success_outcome_state_correct allows writeAllows outputRelation tail
    args observation writeOk Hallowed with "HsuccessCode") as "Hsuccess".
   iSpecialize ("Hsuccess" $! tt).
   iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hsuccess".
   iApply "Hsuccess". iFrame "Hentry".
   iNext. iIntros "Hexit". iDestruct "Hexit" as (bytes) "[%HwriteAllowed Hterminal]".
   iApply "Hreturn". iExists (DecodeBoundarySuccess observation, bytes).
   rewrite /mainWholeAllows /=. iFrame. done.
Qed.
Print Assumptions main_whole_state_correct.

Theorem main_whole_correct
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation) (tail : spec)
 (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64)
 (decodeOk : IslarisContractCorrect 0x12168 0x14cfc
  (mainConcreteDecodeModel allows
   (mainDecodeUnionTail allows
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)))
 (writeOk : IslarisContractCorrect 0x14d30 0x14d10
  (writeSuccessFixedTailModel writeAllows outputRelation
   (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   (fun _ nextPc => nextPc = 0x14d10))) :
 IslarisContractCorrect 0x14cb0 0x101d0
  (mainWholeModel allows writeAllows outputRelation tail
   a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13).
Proof.
 intros Sigma HG HT.
 exact (@main_whole_state_correct Sigma HG HT allows writeAllows outputRelation tail
  a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 decodeOk writeOk).
Qed.
Print Assumptions main_whole_correct.
