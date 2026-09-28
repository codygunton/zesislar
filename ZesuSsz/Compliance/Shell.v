Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
From iris.program_logic Require Import language.
From stdpp Require Import gmap.
Require Import isla.opsem.
Require Import isla.riscv64.riscv64.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Compliance.EvmSailAdapter.
Require Import ZesuSsz.Compliance.BugPredicates.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Compliance.ObservationBridge.
Require Export ZesuSsz.Compliance.TraceObservation.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Compliance.Program.
Require Import ZesuSsz.Compliance.Initial.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.WholeResources.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.

Import ListNotations.
Open Scope Z_scope.

Definition mainEntryPc : Z := ZesuSsz.Generated.Level1.mainEntry.
Definition mainExitPc : Z := ZesuSsz.Generated.Level1.decodeInputEntry.
Definition decodeEntryPc : Z := ZesuSsz.Generated.Level1.decodeInputEntry.
Definition decodeExitPc : Z := 0x14cfc.

Definition zesuOutcomeOfTrace (labels : list seq_label) : option DecodeOutcome :=
  match zesuOutputBytesOfTrace labels with
  | Some bytes =>
      if decide (bytes = failureObservation) then Some DecodeFailure
      else option_map
        (fun observation => DecodeSuccess (observationToStatelessInput observation))
        (writeSuccessDecodeObservation bytes)
  | None => None
  end.

Definition zesuEndpoint (P : AdmissibleProgram) : EndpointSemantics := {|
  endpointRuns := fun input outcome =>
    exists n kappa cfg',
      nsteps n (zesuInitial P input) kappa cfg' /\
      zesuOutcomeOfTrace kappa = Some outcome
|}.

Definition ZesuDecodeBugApplies :=
  KnownBug -> ByteString -> WriteSuccessObservation -> Prop.

Definition zesuObservationBugApplies : ZesuDecodeBugApplies :=
  fun bug input observation =>
    zesuBugApplies bug input
      (DecodeSuccess (observationToStatelessInput observation)).

Lemma zesuObservationBugApplies_agrees bug input outcome :
  zesuObservationBugApplies bug input outcome <->
  zesuBugApplies bug input (DecodeSuccess (observationToStatelessInput outcome)).
Proof. reflexivity. Qed.
Print Assumptions zesuObservationBugApplies_agrees.

Definition DecodeMeaningModuloKnownBugs
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (applies : ZesuDecodeBugApplies)
    (args : DecodeBoundaryArgs)
    (outcome : DecodeBoundaryOutcome WriteSuccessObservation) : Prop :=
  exists ref, inputRef (decodeInput args) = Some ref /\
    match outcome with
    | DecodeBoundaryFailure =>
        ReferenceRejects runner model (decodeInput args) ref
    | DecodeBoundarySuccess observation =>
        ReferenceDecodes runner model (decodeInput args) ref
          (observationToStatelessInput observation) \/
        exists bug, In bug knownBugs /\
          applies bug (decodeInput args) observation
    end.

Definition zesuSuccessArgs
    (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation) :
    WriteSuccessArgs WriteSuccessObservation := {|
  successReturnAddress := 0x14d10;
  successStackPointer := decodeStackPointer args;
  successDecodedAddress := (decodeStackPointer args + 32)%Z;
  successDecoded := observation;
  successInputSize := length (decodeInput args)
|}.

Definition zesuWriteSuccessAllows
    (args : WriteSuccessArgs WriteSuccessObservation)
    (bytes : ByteString) : Prop :=
  bytes = writeSuccessEncodeObservation (successDecoded _ args).

Definition zesuWriteSuccessOutputRelation :
    WriteSuccessOutputRelation WriteSuccessObservation :=
  fun args _ bytes => zesuWriteSuccessAllows args bytes.

Definition zesuWriteSuccessContract :
    IslarisContractModel
      (WriteSuccessArgs WriteSuccessObservation) ByteString :=
  writeSuccessNativeModel zesuWriteSuccessAllows
    zesuWriteSuccessOutputRelation (fun _ _ => True).

Definition zesuDecodeResources
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (applies : ZesuDecodeBugApplies)
    (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG) :
    @IslarisContractResources Sigma HG HT DecodeBoundaryArgs
      (DecodeBoundaryOutcome WriteSuccessObservation) := {|
  islarisCode := True%I;
  islarisEntry := fun _ => True%I;
  islarisExit := fun args outcome =>
    match outcome with
    | DecodeBoundarySuccess observation =>
        islarisEntry _ _
          (islarisContractResources _ _ zesuWriteSuccessContract Sigma HG HT)
          (zesuSuccessArgs args observation)
    | DecodeBoundaryFailure =>
        islarisEntry _ _ (@write_failure_resources Sigma HG HT)
          {| failureReturnAddress := 0x14d24 |}
    end
|}.

Definition zesuDecodeContract
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (applies : ZesuDecodeBugApplies) :
    IslarisContractModel DecodeBoundaryArgs
      (DecodeBoundaryOutcome WriteSuccessObservation) := {|
  islarisContractAllows :=
    DecodeMeaningModuloKnownBugs runner model inputRef applies;
  islarisContractStep := fun _ _ => True;
  islarisContractResources := zesuDecodeResources runner model inputRef applies
|}.

Definition zesuMainResources
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (applies : ZesuDecodeBugApplies)
    (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG) :
    @IslarisContractResources Sigma HG HT unit DecodeBoundaryArgs := {|
  islarisCode := True%I;
  islarisEntry := fun _ => True%I;
  islarisExit := fun _ args =>
    islarisEntry _ _
      (zesuDecodeResources runner model inputRef applies Sigma HG HT) args
|}.

Definition zesuMainContract
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (applies : ZesuDecodeBugApplies) :
    IslarisContractModel unit DecodeBoundaryArgs := {|
  islarisContractAllows := fun _ _ => True;
  islarisContractStep := fun _ _ => True;
  islarisContractResources := zesuMainResources runner model inputRef applies
|}.

Lemma zesuMainDecodeHandoff runner model inputRef applies Sigma HG HT args :
  islarisExit _ _
      (zesuMainResources runner model inputRef applies Sigma HG HT) tt args =
  islarisEntry _ _
      (zesuDecodeResources runner model inputRef applies Sigma HG HT) args.
Proof. reflexivity. Qed.

Lemma zesuDecodeSuccessHandoff runner model inputRef applies Sigma HG HT args observation :
  islarisExit _ _
      (zesuDecodeResources runner model inputRef applies Sigma HG HT) args
      (DecodeBoundarySuccess observation) =
  islarisEntry _ _
      (islarisContractResources _ _ zesuWriteSuccessContract Sigma HG HT)
      (zesuSuccessArgs args observation).
Proof. reflexivity. Qed.

Lemma zesuDecodeFailureHandoff runner model inputRef applies Sigma HG HT args :
  islarisExit _ _
      (zesuDecodeResources runner model inputRef applies Sigma HG HT) args
      DecodeBoundaryFailure =
  islarisEntry _ _ (@write_failure_resources Sigma HG HT)
      {| failureReturnAddress := 0x14d24 |}.
Proof. reflexivity. Qed.

Lemma zesu_decode_meaning_compliance runner model inputRef args outcome expected :
  DecodeMeaningModuloKnownBugs runner model inputRef
    zesuObservationBugApplies args outcome ->
  referenceRuns (EvmSailReference runner model inputRef)
    (decodeInput args) expected ->
  OutcomeEquivalentModulo zesuBugApplies zesuEquivalent (decodeInput args)
    (match outcome with
     | DecodeBoundaryFailure => DecodeFailure
     | DecodeBoundarySuccess observation =>
       DecodeSuccess (observationToStatelessInput observation)
     end) expected.
Proof.
  intros [ref [Hinput Hmeaning]] [expectedRef [HexpectedRef Hexpected]].
  rewrite Hinput in HexpectedRef. inversion HexpectedRef. subst expectedRef.
  unfold OutcomeEquivalentModulo, zesuEquivalent.
  destruct outcome as [|observation]; simpl in Hmeaning |- *.
  - destruct expected as [decoded|]; simpl in Hexpected.
    + unfold ReferenceRejects in Hmeaning. unfold ReferenceDecodes in Hexpected.
      pose proof (evaluates_functional runner _ _ _ _ _ Hmeaning Hexpected) as Heq.
      discriminate.
    + left. reflexivity.
  - destruct Hmeaning as [Hdecoded|Hbug].
    + destruct expected as [decoded|]; simpl in Hexpected.
      * unfold ReferenceDecodes in Hdecoded, Hexpected.
        pose proof (evaluates_functional runner _ _ _ _ _ Hdecoded Hexpected) as Heq.
        inversion Heq. left. reflexivity.
      * unfold ReferenceDecodes in Hdecoded. unfold ReferenceRejects in Hexpected.
        pose proof (evaluates_functional runner _ _ _ _ _ Hdecoded Hexpected) as Heq.
        discriminate.
    + right. exact Hbug.
Qed.
Print Assumptions zesu_decode_meaning_compliance.

Theorem zesuCompliance
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (P : AdmissibleProgram)
    (decodeOk : IslarisContractCorrect 0x12168 0x14cfc
      (mainConcreteDecodeModel
        (DecodeMeaningModuloKnownBugs runner model inputRef
          zesuObservationBugApplies)
        (mainDecodeUnionTail
          (DecodeMeaningModuloKnownBugs runner model inputRef
            zesuObservationBugApplies)
          (fun _ => scons (SWriteMem
            (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) snil)
          (fun _ => scons (SWriteMem
            (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) snil))
        (fun _ => scons (SWriteMem
          (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) snil)))
    (writeOk : IslarisContractCorrect 0x14d30 0x14d10
      (writeSuccessFixedTailModel zesuWriteSuccessAllows
        zesuWriteSuccessOutputRelation
        (scons (SWriteMem
          (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) snil)
        (fun _ nextPc => nextPc = 0x14d10))) :
  ComplianceModuloKnownBugs (zesuEndpoint P)
    (EvmSailReference runner model inputRef) zesuBugApplies zesuEquivalent.
Admitted.

Print Assumptions zesuCompliance.
