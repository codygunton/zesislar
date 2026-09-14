Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.SuccessWitnessBridge.
Require Import ZesuSsz.Proofs.Main.SuccessStatusGlue.
Lemma main_success_after_decode_state_correct `{!islaG Sigma} `{!threadG}
    (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
    (successExitTail failureExitTail : DecodeBoundaryArgs -> spec)
    (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation) :
  allows args (DecodeBoundarySuccess observation) ->
  ⊢ IslarisContractSpec 0x14cfc 0x14d30 (fun _ _ => True%type)
    (mainSuccessAfterDecodeResources allows successExitTail failureExitTail args observation).
Proof.
  intros Hallowed.
  rewrite /IslarisContractSpec /mainSuccessAfterDecodeResources
    /mainDecodeConcreteResources /mainDecodeMachineResources /=.
  iIntros "Hcode" (contractArgs).
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[Hentry Hreturn]".
  iDestruct "Hentry" as (allocatorPointer allocatorSize)
    "(Hregisters&Hcaller&%HsavedLength&%Halign&%Hlow&%Hhigh&%Hsp&%Hsp32&Hobject&_&Hscratch&Hprivate&Houtput&Hspec&Hpreserved)".
  iDestruct "Hregisters" as "(Hsys&Hother&H1&H2&Hsaved&Hargs)".
  iDestruct "Hargs" as (a0 a1 a2) "(H10&H11&H12)".
  iDestruct "Hobject" as (witness) "(%Hwell&%Htail&%Hsaved&Hstatus&Hdecoded&Hdata)".
  iPoseProof (main_success_trace_select allows successExitTail failureExitTail args
    observation witness Hallowed Hwell Htail with "Hspec") as "Hspec".
  pose proof Hwell as Hfacts.
  destruct Hfacts as [HentrySp [HdecodedPtr [_ [_ [_ [Hlength _]]]]]].
  change (decodeStackPointer args = bv_unsigned (writeSuccessEntrySp witness)) in HentrySp.
  change (decodeStackPointer args + 32 = bv_unsigned (writeSuccessDecodedPointer witness)) in HdecodedPtr.
  iAssert (writeSuccessProloguePayload witness)
    with "[Hprivate Hdecoded Houtput Hspec Hdata]" as "Hpayload".
  { rewrite /writeSuccessProloguePayload.
    iFrame "Hdecoded Houtput Hspec Hdata". rewrite -HentrySp. iFrame "Hprivate".
    repeat iSplit; iPureIntro; first exact Hlength.
    all: first [done | rewrite -HdecodedPtr; zesu_normalize_machine_map; lia]. }
  iPoseProof (main_success_status_glue_state_correct
    (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14cfc) a0 a1
    (mainSuccessWitnessFrame args witness a2 allocatorPointer allocatorSize)
    with "Hcode") as "Hglue".
  iSpecialize ("Hglue" $! tt).
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hglue".
  iApply "Hglue".
  iSplitL "Hsys Hother H1 H2 Hsaved H10 H11 H12 Hcaller Hstatus Hscratch Hpayload Hpreserved".
  { rewrite /mainSuccessStatusGlueResources /mainCallRegisters
      /mainDispatchMemory /mainSuccessWitnessFrame /= Hsp.
    have Hsp880 : bv_unsigned (Z_to_bv 64 (decodeStackPointer args) + BV 64 880)%bv = decodeStackPointer args + 880.
    { pose proof (main_prefix_stack_offset _ 880 Hlow Hhigh ltac:(lia)). bv_solve. }
    iEval (rewrite -Hsp880) in "Hstatus".
    iFrame. repeat iSplit; iPureIntro; try done;
      zesu_normalize_machine_map; lia. }
  iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
  iApply "Hreturn". iExists tt. iSplit; first done.
  iExists allocatorPointer, allocatorSize.
  iApply (main_success_witness_fixed_tail_entry args observation witness
    (successExitTail args) a1 a2 allocatorPointer allocatorSize
    Hwell Htail Hsaved Halign Hlow Hhigh Hsp Hsp32 with "Hexit").
Qed.
Print Assumptions main_success_after_decode_state_correct.
