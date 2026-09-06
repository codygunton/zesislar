From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Generated.WriteSuccessCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessCfgCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessNativeBridge.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessNativeEpilogue.
Require Import ZesuSsz.Experiments.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessNativeOutputRelation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessHostObservation.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeader.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentedPrefix.

Import ListNotations.
Open Scope Z_scope.

(** These projections must read fields from the concrete decoded value and
    from the owned native memory layout.  They do not mention the decoder. *)
Record WriteSuccessStructuralProjections (Decoded : Type) : Type := {
  writeSuccessDecodedObservation : Decoded -> WriteSuccessObservation;
  writeSuccessDecodedMemoryRepresents :
    Decoded -> list (bv 8) -> Prop
}.

Definition writeSuccessWitnessRepresents {Decoded}
    (projections : WriteSuccessStructuralProjections Decoded)
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (observation : WriteSuccessObservation) : Prop :=
  writeSuccessDecodedMemoryRepresents Decoded projections
    (successDecoded Decoded args) (writeSuccessDecodedBytes witness) /\
  writeSuccessDecodedObservation Decoded projections
    (successDecoded Decoded args) = observation /\
  writeSuccessObservationValid observation.

(** The representation proof must cover every permitted argument and native
    witness.  A proof cannot use the decoder conclusion as a premise. *)
Definition WriteSuccessRepresentationInterface {Decoded}
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  forall args witness,
    writeSuccessDecodedMemoryRepresents Decoded projections
      (successDecoded Decoded args) (writeSuccessDecodedBytes witness) ->
    exists observation,
      writeSuccessWitnessRepresents projections args witness observation.

Definition writeSuccessIdentityProjections
    (memoryRepresents : WriteSuccessObservation -> list (bv 8) -> Prop) :
    WriteSuccessStructuralProjections WriteSuccessObservation := {|
  writeSuccessDecodedObservation := fun observation => observation;
  writeSuccessDecodedMemoryRepresents := memoryRepresents
|}.

Lemma writeSuccessCp1RepresentationExample memoryRepresents :
  (forall (args : WriteSuccessArgs WriteSuccessObservation)
      (witness : writeSuccessNativeWitness WriteSuccessObservation),
    memoryRepresents (successDecoded WriteSuccessObservation args)
      (writeSuccessDecodedBytes witness) ->
    writeSuccessObservationValid
      (successDecoded WriteSuccessObservation args)) ->
  WriteSuccessRepresentationInterface
    (writeSuccessIdentityProjections memoryRepresents).
Proof.
  intros Hprojection args witness Hmemory.
  exists (successDecoded WriteSuccessObservation args).
  exact (conj Hmemory (conj eq_refl (Hprojection args witness Hmemory))).
Qed.

(** This interface derives the encoded bytes from ordered memory snapshots.
    The write index distinguishes repeated writes from the same address. *)
Definition writeOutputExecutionObservation
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (eventStates : list (seq_local_state * seq_global_state))
    (descriptors : list WriteOutputDescriptor) (bytes : ByteString) : Prop :=
  exists payloads : list (list (bv 8)),
    WriteSuccessRepeatedExecutionObservations initialLocal initialState
      eventStates descriptors payloads /\
    bytes = writeSuccessPublicBytes (concat payloads).

Definition writeSuccessExecutionOutputRelation {Decoded} :
    WriteSuccessOutputRelation Decoded :=
  fun _ witness bytes =>
    exists initialLocal initialState eventStates,
      writeOutputExecutionObservation initialLocal initialState eventStates
        (writeSuccessNativeDescriptors witness) bytes.

Definition WriteSuccessOutputInterface {Decoded}
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  forall args witness observation bytes,
    writeSuccessWitnessRepresents projections args witness observation ->
    writeSuccessExecutionOutputRelation args witness bytes ->
    bytes = writeSuccessEncodeObservation observation.

(** This resource is the exact [0x14d80] handoff from the proved prefix. *)
Definition writeSuccessLoadExitResources `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  writeSuccessAtLoadHeaderWithFrame
    (writeSuccessFrameSp witness)
    (take 720 (writeSuccessDecodedBytes witness))
    (writeSuccessNativeTailEvents witness)
    (reg_col writeSuccessLoadHeaderExtraRegisters ∗
     writeSuccessNativeDataResources witness).

Global Instance : LithiumUnfold (@writeSuccessLoadExitResources) := I.

Definition writeSuccessFinalContinuation `{!islaG Sigma} `{!threadG}
    {State Decoded} (model : Level1MachineModel State Decoded)
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  instr_pre 0x14d10
    (∃ bytes : ByteString,
      ⌜writeSuccessNativeAllows model args bytes⌝ ∗
      writeSuccessTerminalResources
        writeSuccessExecutionOutputRelation args bytes).

Global Instance : LithiumUnfold (@writeSuccessFinalContinuation) := I.

Definition writeSuccessConcreteDecodeMeaning {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  forall bytes decoded,
    decodeObservationSuccess State Decoded model bytes decoded <->
    writeSuccessDecodeObservation bytes =
      Some (writeSuccessDecodedObservation Decoded projections decoded).

(** The suffix proof starts with the exact load resources.  It preserves the
    final continuation until the epilogue reaches [0x14d10]. *)
Definition WriteSuccessMachineSuffixInterface {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  WriteSuccessRepresentationInterface projections ->
  WriteSuccessOutputInterface projections ->
  writeSuccessConcreteDecodeMeaning model projections ->
  writeSuccessObservationRoundTrip ->
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ writeSuccessNativeCode -∗
      ∀ args : WriteSuccessArgs Decoded,
      instr_body 0x14d80
        ((∃ (witness : writeSuccessNativeWitness Decoded)
             (observation : WriteSuccessObservation),
            ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
            ⌜writeSuccessWitnessRepresents
              projections args witness observation⌝ ∗
            writeSuccessLoadExitResources witness) ∗
         writeSuccessFinalContinuation model args).

(** This interface contains only the exact suffix proof.  The theorem below
    composes that proof with the compiled public-entry prefix. *)
Definition WriteSuccessMachineInterface {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  WriteSuccessMachineSuffixInterface model projections.

Definition writeSuccessCorrectedNativeResources {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded)
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (WriteSuccessArgs Decoded) ByteString := {|
  islarisCode := writeSuccessNativeCode;
  islarisEntry := writeSuccessRepresentedNativeEntry
    (writeSuccessDecodedMemoryRepresents Decoded projections);
  islarisExit := writeSuccessTerminalResources
    writeSuccessExecutionOutputRelation
|}.

Definition writeSuccessCorrectedNativeModel {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded)
    (nextPc : Z -> Z -> Prop) :
    IslarisContractModel (WriteSuccessArgs Decoded) ByteString := {|
  islarisContractAllows := writeSuccessNativeAllows model;
  islarisContractStep := nextPc;
  islarisContractResources := fun Sigma HG HT =>
    @writeSuccessCorrectedNativeResources State Decoded model projections
      Sigma HG HT
|}.

Definition writeSuccessCorrectedNativeCorrectness {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessCorrectedNativeModel model projections
      writeSuccessGeneratedInstructionStep).

Theorem writeSuccessMachineComposition {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) :
  WriteSuccessRepresentationInterface projections ->
  WriteSuccessOutputInterface projections ->
  writeSuccessConcreteDecodeMeaning model projections ->
  writeSuccessObservationRoundTrip ->
  WriteSuccessMachineInterface model projections ->
  writeSuccessCorrectedNativeCorrectness model projections.
Proof.
  intros Hrepresentation Houtput Hdecode HroundTrip Hsuffix Sigma HG HT.
  rewrite /writeSuccessCorrectedNativeCorrectness /IslarisContractCorrect
    /IslarisContractSpec /writeSuccessCorrectedNativeModel
    /writeSuccessCorrectedNativeResources /=.
  iIntros "#Hcode" (args).
  pose proof (Hsuffix Hrepresentation Houtput Hdecode HroundTrip
    Sigma HG HT) as HsuffixProof.
  iPoseProof (HsuffixProof with "Hcode") as "Hsuffix".
  iSpecialize ("Hsuffix" $! args).
  iPoseProof (write_success_represented_prefix_correct
    (writeSuccessDecodedMemoryRepresents Decoded projections)) as "Hprefix".
  iSpecialize ("Hprefix" with "Hcode").
  iSpecialize ("Hprefix" $! args).
  iApply (instr_pre_wand with "Hprefix"); [done | done |].
  iIntros "[Hentry Hfinal]". iFrame "Hentry".
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand with "Hsuffix"); [done | reflexivity |].
  iIntros "Hresult".
  iDestruct "Hresult" as (witness) "[%Hallows Hload]".
  destruct Hallows as [Hwell Hmemory].
  destruct (Hrepresentation args witness Hmemory)
    as [observation Hrepresents].
  iSplitL "Hload".
  - iExists witness, observation. iFrame.
    iPureIntro. split; assumption.
  - iExact "Hfinal".
Qed.

(** The termination interface contains local obligations for actual stopped
    transitions.  All permitted nonterminal successors preserve the invariant
    and decrease the natural rank. *)
Definition WriteSuccessTerminationInterface {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : nat -> nat) : Type :=
  DecreasingExecutionObligations
    (endpointStep State Decoded model)
    (endpointPc State Decoded model)
    (ZesuSsz.Contracts.Level1.writeSuccessEntry State Decoded model)
    (PcInRanges writeSuccessExecutionPcRanges)
    (PcInList writeSuccessExitPcs)
    ZesuSsz.Generated.Level1.writeSuccessEntry
    (fun args => bound (successInputSize Decoded args)).

Theorem writeSuccessTerminationExecution {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : nat -> nat)
    (termination : WriteSuccessTerminationInterface model bound) :
  ExecutionPathCertificate
    (endpointStep State Decoded model)
    (endpointPc State Decoded model)
    (ZesuSsz.Contracts.Level1.writeSuccessEntry State Decoded model)
    (PcInRanges writeSuccessExecutionPcRanges)
    (PcInList writeSuccessExitPcs)
    ZesuSsz.Generated.Level1.writeSuccessEntry
    (fun args => bound (successInputSize Decoded args)).
Proof. exact (executionCertificateFromDecrease _ _ _ _ _ _ _ termination). Qed.

Lemma writeSuccessInterfacesSemantic {State Decoded}
    (model : Level1MachineModel State Decoded)
    (projections : WriteSuccessStructuralProjections Decoded) :
  WriteSuccessOutputInterface projections ->
  writeSuccessConcreteDecodeMeaning model projections ->
  writeSuccessObservationRoundTrip ->
  forall args witness observation bytes,
    writeSuccessWitnessRepresents projections args witness observation ->
    writeSuccessExecutionOutputRelation args witness bytes ->
    decodeObservationSuccess State Decoded model bytes
      (successDecoded Decoded args).
Proof.
  intros Houtput Hdecode HroundTrip args witness observation bytes
    Hrep Hbytes.
  apply Hdecode.
  destruct Hrep as (Hmemory & Hdecoded & Hvalid).
  assert (Hrep : writeSuccessWitnessRepresents projections args witness observation).
  { exact (conj Hmemory (conj Hdecoded Hvalid)). }
  pose proof (Houtput args witness observation bytes Hrep Hbytes) as Hencoded.
  rewrite Hdecoded.
  unfold writeSuccessDecodeObservation. rewrite Hencoded.
  pose proof (HroundTrip observation [] Hvalid) as Hparse.
  rewrite app_nil_r in Hparse. rewrite Hparse. reflexivity.
Qed.

Print Assumptions writeSuccessTerminationExecution.
Print Assumptions writeSuccessInterfacesSemantic.
Print Assumptions writeSuccessCp1RepresentationExample.
Print Assumptions nativeExecutionContractBridge.
