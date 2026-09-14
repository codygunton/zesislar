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

Lemma main_success_writer_terminal_entry `{!islaG Sigma} `{!threadG}
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation)
 (tail : spec) (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation)
 (bytes : ByteString) (allocatorPointer allocatorSize : bv 64) :
 writeSuccessFixedTailTerminalResources outputRelation
  (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
  (mainWriterArgs args observation) bytes ∗ mainSuccessCallerFrame args allocatorPointer allocatorSize ⊢
 ∃ (witness : writeSuccessNativeWitness WriteSuccessObservation) (a0 a1 a2 x5 x6 : bv 64),
 ⌜writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness⌝ ∗
 ⌜outputRelation (mainWriterArgs args observation) witness bytes⌝ ∗
 islarisEntry _ _ (mainSuccessFinishResources tail (Z_to_bv 64 (decodeStackPointer args))
  a0 a1 x5 x6 (mainSuccessWriterTerminalFrame args witness allocatorPointer allocatorSize a2)) tt.
Proof.
 rewrite /writeSuccessFixedTailTerminalResources /writeSuccessExactTerminalMachine.
 iIntros "[Hterminal Hcaller]".
 iDestruct "Hterminal" as (witness) "(%Hwell&%Htail&%Houtput&(Hmachine&Hreturned)&Hmemory&Hspec)".
 iDestruct "Hreturned" as (a0 a1 a2) "(H10&H11&H12)".
 iEval (rewrite /writeSuccessTerminalMachine) in "Hmachine".
 iDestruct "Hmachine" as "(Hsys&Hother&H1&H2&H8&H9&H18&H19&H20&H21&H22&H23&H24&H25&H26&H27&Hslots)".
 iPoseProof (main_returned_other_registers with "Hother") as "Hother".
 iDestruct "Hother" as (x5 x6) "(H5&H6&Hother)".
 pose proof Hwell as Hfacts.
 destruct Hfacts as [HentrySp [_ [_ [HreturnValue _]]]].
 change (decodeStackPointer args = bv_unsigned (writeSuccessEntrySp witness)) in HentrySp.
 have HentryValue : Z_to_bv 64 (decodeStackPointer args) = writeSuccessEntrySp witness.
 { rewrite HentrySp. apply bv_eq. rewrite Z_to_bv_unsigned bv_wrap_bv_unsigned. done. }
 change (writeSuccessReturnValue witness = Z_to_bv 64 0x14d10) in HreturnValue.
 have HreturnBits : writeSuccessReturnValue witness = BV 64 0x14d10.
 { rewrite HreturnValue. apply bv_eq. vm_compute. reflexivity. }
 iEval (rewrite /mainSuccessCallerFrame mainDecoderPreservedFrame_separate_exit) in "Hcaller".
 iDestruct "Hcaller" as "(Hcaller&Hstatus&(Hpreserved&Hexit)&_)".
 iExists witness, a0, a1, a2, x5, x6. iSplit; first done. iSplit; first done.
 rewrite /mainSuccessFinishResources /mainCallRegisters /mainSuccessWriterTerminalFrame
  /mainSuccessReturnedCallerFrame /= HentryValue HreturnBits.
 iFrame.
Qed.
Print Assumptions main_success_writer_terminal_entry.

Lemma main_failure_concrete_entry `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (successExitTail : DecodeBoundaryArgs -> spec) (tail : spec) (args : DecodeBoundaryArgs) :
 allows args DecodeBoundaryFailure ->
 islarisExit _ _ (mainDecodeConcreteResources
  (mainDecodeUnionTail allows successExitTail
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
  successExitTail) args DecodeBoundaryFailure ⊢
 ∃ (status : bv 16) (allocatorPointer allocatorSize a2 : bv 64) (objectBytes : list (bv 8)),
 ⌜status <> BV 16 0⌝ ∗ ⌜length objectBytes = 848%nat⌝ ∗
 islarisEntry _ _ (mainFailureAfterDecodeResources tail
  (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14cfc) status
  (mainFailureDecoderFrame args allocatorPointer allocatorSize a2 objectBytes)) tt.
Proof.
 intros Hallowed.
 rewrite /mainDecodeConcreteResources /mainDecodeMachineResources /=.
 iIntros "Hentry".
 iDestruct "Hentry" as (allocatorPointer allocatorSize)
 "(Hregisters&Hcaller&%HsavedLength&%Halign&%Hlow&%Hhigh&%Hsp&%Hsp32&Hobject&Hheap&Hscratch&Hprivate&Houtput&Hspec&Hpreserved)".
 iEval (rewrite /mainDecoderObjectResources /=) in "Hobject".
 iDestruct "Hobject" as (status objectBytes) "(%Hstatus&%HobjectLength&Hstatus&Hobject)".
 iEval (rewrite /mainDecoderRegisters) in "Hregisters".
 iDestruct "Hregisters" as "(Hsys&Hother&H1&H2&Hsaved&Hargs)".
 iDestruct "Hargs" as (a0 a1 a2) "(H10&H11&H12)".
 iPoseProof (main_returned_other_registers with "Hother") as "Hother".
 iDestruct "Hother" as (x5 x6) "(H5&H6&Hother)".
 iPoseProof (main_failure_trace_select _ _ _ _ Hallowed with "Hspec") as "Hspec".
 iEval (rewrite mainDecoderPreservedFrame_separate_exit
  mainDecoderPreservedMemoryFrame_separate_failure) in "Hpreserved".
 iDestruct "Hpreserved" as "[(Hpreserved&Hfailure) Hexit]".
 have Hnonzero : bv_unsigned status <> 0.
 { intros Hz. apply Hstatus. apply bv_eq. rewrite Hz. vm_compute. reflexivity. }
 have Halign8 : decodeStackPointer args `mod` 8 = 0.
 { exact (proj1 (main_prefix_stack_alignment _ Halign Hlow Hhigh)). }
 have Hsp880 : bv_unsigned (Z_to_bv 64 (decodeStackPointer args) + BV 64 880)%bv = decodeStackPointer args + 880.
 { pose proof (main_prefix_stack_offset _ 880 Hlow Hhigh ltac:(lia)). bv_solve. }
 iEval (rewrite /mainFailurePayloadAddress; zesu_normalize_machine_map) in "Hfailure".
 iExists status, allocatorPointer, allocatorSize, a2, objectBytes.
 iSplit; first done. iSplit; first done.
 rewrite /mainFailureAfterDecodeResources /mainFailureOutcomeResources /=.
 iSplit; first done.
 iSplitL "Hstatus".
 { rewrite /mainDispatchMemory Hsp Hsp880. iFrame.
   repeat iSplit; iPureIntro; first exact Halign8.
   all: first [done | zesu_normalize_machine_map; lia]. }
 iExists x5, x6, a0, a1.
 rewrite /mainCallRegisters /mainFailureDecoderFrame /=.
 iFrame.
Qed.
Print Assumptions main_failure_concrete_entry.
