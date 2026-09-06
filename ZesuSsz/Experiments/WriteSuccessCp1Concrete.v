From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.opsem.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Generated.WriteSuccessCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentedPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteMachine.
Require Import ZesuSsz.Experiments.WriteSuccessReviewInterfaces.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessConcreteProjections :
    WriteSuccessStructuralProjections WriteSuccessObservation :=
  writeSuccessIdentityProjections writeSuccessConcreteBytesRepresentation.

Lemma writeSuccessConcreteBytesRepresentationValid decoded bytes :
  writeSuccessConcreteBytesRepresentation decoded bytes ->
  writeSuccessObservationValid decoded.
Proof.
  intros (memory & address & Hrepresentation & _).
  exact (proj1 Hrepresentation).
Qed.

Lemma writeSuccessConcreteLoadRepresentationExamples
    `{!islaG Sigma} `{!threadG}
    (decoded : WriteSuccessObservation)
    (witness : writeSuccessNativeWitness WriteSuccessObservation) :
  ⌜writeSuccessConcreteBytesRepresentation
      decoded (writeSuccessDecodedBytes witness)⌝ ∗
  writeSuccessLoadExitResources witness -∗
  ∃ memory address,
    ⌜writeSuccessConcreteRepresentation decoded memory address /\
      read_mem_list memory address 848%N =
        Some (writeSuccessDecodedBytes witness) /\
      writeSuccessMemoryInteger memory (address + 48) 8
        (observationBaseFee decoded) /\
      writeSuccessMemorySlice memory address 32
        (observationExtraData decoded)⌝ ∗
    writeSuccessLoadExitResources witness.
Proof.
  iIntros "[%Hrepresentation Hload]".
  destruct Hrepresentation as
    (memory & address & Hstructural & Htop).
  iExists memory, address. iFrame.
  iPureIntro.
  exact (conj Hstructural (conj Htop
    (conj (writeSuccessRepresentationBaseFee _ _ _ Hstructural)
      (writeSuccessRepresentationExtraData _ _ _ Hstructural)))).
Qed.

Lemma writeSuccessConcreteRepresentationInterface :
  WriteSuccessRepresentationInterface writeSuccessConcreteProjections.
Proof.
  apply writeSuccessCp1RepresentationExample.
  intros args witness Hrepresentation.
  exact (writeSuccessConcreteBytesRepresentationValid _ _ Hrepresentation).
Qed.

Lemma writeSuccessConcreteDecodeAgreement :
  writeSuccessConcreteDecodeMeaning
    writeSuccessConcreteModel writeSuccessConcreteProjections.
Proof. intros bytes decoded. reflexivity. Qed.

Lemma writeSuccessConcreteCallerBoundary args state :
  ZesuSsz.Contracts.Level1.writeSuccessEntry
      WriteSuccessConcreteState WriteSuccessObservation
      writeSuccessConcreteModel args state <->
  writeSuccessConcreteEntry args state.
Proof. reflexivity. Qed.

Lemma writeSuccessConcreteCallerRepresentation args state :
  ZesuSsz.Contracts.Level1.writeSuccessEntry
      WriteSuccessConcreteState WriteSuccessObservation
      writeSuccessConcreteModel args state ->
  exists address,
    writeSuccessConcreteDecodedPointer state = Some address /\
    writeSuccessConcreteRepresentation
      (successDecoded WriteSuccessObservation args)
      (seq_mem (snd state)) address.
Proof.
  apply writeSuccessConcreteModelRepresentation.
Qed.

(** This is the exact caller-to-Islaris resource refinement that remains for
    the complete proof.  It relates the concrete entry state to the same
    represented entry resource used by native correctness. *)
Definition WriteSuccessConcreteEntryRefinement : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG)
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState),
    ⊢ writeSuccessConcreteEntryResources args state -∗
      writeSuccessRepresentedNativeEntry
        writeSuccessConcreteBytesRepresentation args.

Theorem writeSuccessConcreteEntryRefinementProved :
  WriteSuccessConcreteEntryRefinement.
Proof.
  intros Sigma HG HT args state.
  rewrite /writeSuccessConcreteEntryResources.
  iIntros "(Hstate & Hthread & Hnative & %Hentry)".
  iDestruct (writeSuccessNativeEntryDecodedBytesAccess with "Hnative") as
    (witness Hwell) "(Hbytes & Hclose)".
  iDestruct (writeSuccessConcreteOwnedEntryRepresentation
    args state witness Hentry Hwell with "[Hstate Hbytes]") as
    "(%Hrepresentation & Hstate & Hbytes)".
  { iFrame. }
  iDestruct ("Hclose" with "Hbytes") as "Hprologue".
  rewrite /writeSuccessRepresentedNativeEntry
    /writeSuccessNativeRepresentation.
  iExists witness. iFrame "%". iExact "Hprologue".
Qed.

(** This contract uses the same concrete state at the Iris entry and in the
    endpoint execution relation. *)
Definition writeSuccessConcreteContractResources
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources
      (WriteSuccessArgs WriteSuccessObservation) ByteString := {|
  islarisCode := writeSuccessNativeCode;
  islarisEntry := fun args =>
    (∃ state : WriteSuccessConcreteState,
      writeSuccessConcreteEntryResources args state)%I;
  islarisExit := writeSuccessTerminalResources
    writeSuccessExecutionOutputRelation
|}.

Definition writeSuccessConcreteContractModel :
    IslarisContractModel
      (WriteSuccessArgs WriteSuccessObservation) ByteString := {|
  islarisContractAllows := writeSuccessNativeAllows writeSuccessConcreteModel;
  islarisContractStep := writeSuccessGeneratedInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @writeSuccessConcreteContractResources Sigma HG HT
|}.

Definition writeSuccessConcreteResourceCorrectness : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    writeSuccessConcreteContractModel.

Theorem writeSuccessConcreteEntryComposition :
  WriteSuccessConcreteEntryRefinement ->
  writeSuccessCorrectedNativeCorrectness
    writeSuccessConcreteModel writeSuccessConcreteProjections ->
  writeSuccessConcreteResourceCorrectness.
Proof.
  intros Hentry Hnative Sigma HG HT.
  rewrite /writeSuccessConcreteResourceCorrectness
    /IslarisContractCorrect /IslarisContractSpec
    /writeSuccessConcreteContractModel
    /writeSuccessConcreteContractResources /=.
  iIntros "#Hcode" (args).
  pose proof (Hnative Sigma HG HT) as HnativeProof.
  iPoseProof (HnativeProof with "Hcode") as "Hnative".
  iSpecialize ("Hnative" $! args).
  iApply (instr_pre_wand with "Hnative"); [done | done |].
  iIntros "[Hentry Hexit]".
  iDestruct "Hentry" as (state) "Hentry".
  pose proof (Hentry Sigma HG HT args state) as Hrefine.
  iPoseProof (Hrefine with "Hentry") as "Hentry".
  iFrame.
Qed.

Theorem writeSuccessConcreteConditionalComposition :
  WriteSuccessOutputInterface writeSuccessConcreteProjections ->
  writeSuccessObservationRoundTrip ->
  WriteSuccessMachineInterface
    writeSuccessConcreteModel writeSuccessConcreteProjections ->
  writeSuccessCorrectedNativeCorrectness
    writeSuccessConcreteModel writeSuccessConcreteProjections.
Proof.
  intros Houtput HroundTrip Hmachine.
  exact (writeSuccessMachineComposition
    writeSuccessConcreteModel writeSuccessConcreteProjections
    writeSuccessConcreteRepresentationInterface Houtput
    writeSuccessConcreteDecodeAgreement HroundTrip Hmachine).
Qed.

Definition WriteSuccessConcreteCp1Result : Prop :=
  exists bound : nat -> nat,
    InputIndexedBound bound /\
    WriteSuccessConcreteEntryRefinement /\
    NativeExecutionContractAssumption
      writeSuccessConcreteResourceCorrectness
      (endpointStep _ _ writeSuccessConcreteModel)
      (endpointPc _ _ writeSuccessConcreteModel)
      (ZesuSsz.Contracts.Level1.writeSuccessEntry _ _
        writeSuccessConcreteModel)
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs)
      ZesuSsz.Generated.Level1.writeSuccessEntry
      (fun args => bound (successInputSize WriteSuccessObservation args)).

Theorem writeSuccessCp1ConditionalComposition (bound : nat -> nat) :
  InputIndexedBound bound ->
  WriteSuccessOutputInterface writeSuccessConcreteProjections ->
  writeSuccessObservationRoundTrip ->
  WriteSuccessMachineInterface
    writeSuccessConcreteModel writeSuccessConcreteProjections ->
  WriteSuccessTerminationInterface writeSuccessConcreteModel bound ->
  WriteSuccessConcreteCp1Result.
Proof.
  intros Hbound Houtput HroundTrip Hmachine Htermination.
  exists bound. split; first exact Hbound.
  split; first exact writeSuccessConcreteEntryRefinementProved.
  apply nativeExecutionContractBridge.
  - apply writeSuccessConcreteEntryComposition.
    { exact writeSuccessConcreteEntryRefinementProved. }
    exact (writeSuccessConcreteConditionalComposition
      Houtput HroundTrip Hmachine).
  - exact (writeSuccessTerminationExecution
      writeSuccessConcreteModel bound Htermination).
Qed.

Print Assumptions writeSuccessConcreteRepresentationInterface.
Print Assumptions writeSuccessConcreteLoadRepresentationExamples.
Print Assumptions writeSuccessConcreteCallerBoundary.
Print Assumptions writeSuccessConcreteCallerRepresentation.
Print Assumptions writeSuccessConcreteConditionalComposition.
Print Assumptions writeSuccessConcreteEntryRefinementProved.
Print Assumptions writeSuccessConcreteEntryComposition.
Print Assumptions writeSuccessCp1ConditionalComposition.
