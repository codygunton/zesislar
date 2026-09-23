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
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Proofs.Main.SnapshotInput.
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

Definition zesuInitialLocal : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := <["PC" := RVal_Bits (BV 64 mainEntryPc)]> ∅;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition zesuInitialGlobal : seq_global_state := {|
  seq_instrs := ∅;
  seq_mem := ∅
|}.

Definition zesuInitial : cfg isla_lang :=
  ([zesuInitialLocal], zesuInitialGlobal).

Fixpoint zesuOutputPayloadsOfTrace
    (labels : list seq_label) : option (list ByteString) :=
  match labels with
  | [] => Some []
  | label :: rest =>
      match label, rest with
      | SWriteMem address data _,
          SWriteMem sizeAddress size snapshot :: remaining =>
          if decide (address = BV 64 (machineOutputAddress defaultMap) /\
                     sizeAddress = BV 64 (machineOutputSizeAddress defaultMap)) then
            match read_mem_list snapshot.(snap_mem) (bvn_unsigned data)
                    (Z.to_N (bvn_unsigned size)),
                  zesuOutputPayloadsOfTrace remaining with
            | Some bytes, Some payloads =>
                Some (List.map bv_unsigned bytes :: payloads)
            | _, _ => None
            end
          else zesuOutputPayloadsOfTrace rest
      | _, _ => zesuOutputPayloadsOfTrace rest
      end
  end.

Definition zesuOutputBytesOfTrace (labels : list seq_label) : option ByteString :=
  (@List.concat Z) <$> zesuOutputPayloadsOfTrace labels.

Lemma zesuOutputPayloadsOfTrace_write data size firstSnapshot writeSnapshot
    labels payload payloads :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
    (Z.to_N (bvn_unsigned size)) = Some payload ->
  zesuOutputPayloadsOfTrace labels = Some payloads ->
  zesuOutputPayloadsOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload :: payloads).
Proof.
  intros Hread Hrest. simpl.
  rewrite Hread Hrest. reflexivity.
Qed.

Lemma zesuOutputBytesOfTrace_write data size firstSnapshot writeSnapshot
    labels payload :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
    (Z.to_N (bvn_unsigned size)) = Some payload ->
  zesuOutputPayloadsOfTrace labels = Some [] ->
  zesuOutputBytesOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload).
Proof.
  intros Hread Hrest. unfold zesuOutputBytesOfTrace.
  rewrite (zesuOutputPayloadsOfTrace_write _ _ _ _ _ _ _ Hread Hrest).
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma zesuOutputBytesOfTrace_write_events data size payload tail
    firstSnapshot writeSnapshot labels :
  writeOutputEvents data size payload tail
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) ->
  zesuOutputPayloadsOfTrace labels = Some [] ->
  zesuOutputBytesOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload).
Proof.
  intros Hspec Hrest.
  apply zesuOutputBytesOfTrace_write; last exact Hrest.
  eapply write_output_events_payload. exact Hspec.
Qed.

Definition zesuOutcomeOfTrace (labels : list seq_label) : option DecodeOutcome :=
  match zesuOutputBytesOfTrace labels with
  | Some bytes =>
      if decide (bytes = failureObservation) then Some DecodeFailure
      else option_map
        (fun observation => DecodeSuccess (observationToStatelessInput observation))
        (writeSuccessDecodeObservation bytes)
  | None => None
  end.

Definition zesuInputOfTrace : list seq_label -> option ByteString :=
  mainInputOfTrace.

Lemma zesuInputOfTrace_bytes labels input :
  zesuInputOfTrace labels = Some input ->
  Forall (fun value => (0 <= value < 256)%Z) input.
Proof. apply main_trace_input_bytes. Qed.
Print Assumptions zesuInputOfTrace_bytes.

Lemma zesuOutcomeOfTrace_failure labels :
  zesuOutputBytesOfTrace labels = Some failureObservation ->
  zesuOutcomeOfTrace labels = Some DecodeFailure.
Proof.
  intros Hbytes. unfold zesuOutcomeOfTrace. rewrite Hbytes.
  destruct (decide (failureObservation = failureObservation));
    [reflexivity | contradiction].
Qed.
Print Assumptions zesuOutcomeOfTrace_failure.

Lemma zesuOutcomeOfTrace_success labels observation :
  writeSuccessObservationValid observation ->
  zesuOutputBytesOfTrace labels =
    Some (writeSuccessEncodeObservation observation) ->
  zesuOutcomeOfTrace labels =
    Some (DecodeSuccess (observationToStatelessInput observation)).
Proof.
  intros Hvalid Hbytes. unfold zesuOutcomeOfTrace. rewrite Hbytes.
  destruct (decide
    (writeSuccessEncodeObservation observation = failureObservation))
    as [Heq|Hneq].
  - unfold writeSuccessEncodeObservation, failureObservation in Heq.
    simpl in Heq. discriminate.
  - rewrite (writeSuccessObservationDecodeEncode observation Hvalid).
    reflexivity.
Qed.
Print Assumptions zesuOutcomeOfTrace_success.

Definition zesuEndpoint : EndpointSemantics := {|
  endpointRuns := fun input outcome =>
    exists n kappa cfg',
      nsteps n zesuInitial kappa cfg' /\
      zesuInputOfTrace kappa = Some input /\
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

Definition zesuDecodeOutcome
    (outcome : DecodeBoundaryOutcome WriteSuccessObservation) : DecodeOutcome :=
  match outcome with
  | DecodeBoundaryFailure => DecodeFailure
  | DecodeBoundarySuccess observation =>
      DecodeSuccess (observationToStatelessInput observation)
  end.

Lemma zesuDecodeMeaningReference
    runner model inputRef args outcome expected :
  DecodeMeaningModuloKnownBugs runner model inputRef
    zesuObservationBugApplies args outcome ->
  referenceRuns (EvmSailReference runner model inputRef)
    (decodeInput args) expected ->
  OutcomeEquivalentModulo zesuBugApplies zesuEquivalent
    (decodeInput args) (zesuDecodeOutcome outcome) expected.
Proof.
  intros (ref & Href & Hmeaning) (expectedRef & HexpectedRef & Hexpected).
  rewrite Href in HexpectedRef. inversion HexpectedRef; subst expectedRef.
  destruct outcome as [|observation]; simpl in *.
  - destruct expected as [decoded|]; simpl in *.
    + exfalso. unfold ReferenceRejects, ReferenceDecodes in *.
      pose proof (evaluates_functional runner _ _ _ _ _ Hmeaning Hexpected)
        as Hresults. discriminate.
    + left. reflexivity.
  - destruct Hmeaning as [Hsame|[bug [Hin Hbug]]].
    + destruct expected as [decoded|]; simpl in *.
      * left. unfold zesuEquivalent. f_equal.
        unfold ReferenceDecodes in *.
        pose proof (evaluates_functional runner _ _ _ _ _ Hsame Hexpected)
          as Hresults. inversion Hresults. reflexivity.
      * exfalso. unfold ReferenceDecodes, ReferenceRejects in *.
        pose proof (evaluates_functional runner _ _ _ _ _ Hsame Hexpected)
          as Hresults. discriminate.
    + right. exists bug. split; first exact Hin. exact Hbug.
Qed.
Print Assumptions zesuDecodeMeaningReference.

Theorem zesuCompliance
    (runner : DecoderEvaluator) (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef)
    (mainOk : IslarisContractCorrect mainEntryPc mainExitPc
      (zesuMainContract runner model inputRef zesuObservationBugApplies))
    (decodeOk : IslarisContractCorrect decodeEntryPc decodeExitPc
      (zesuDecodeContract runner model inputRef zesuObservationBugApplies)) :
  ComplianceModuloKnownBugs zesuEndpoint
    (EvmSailReference runner model inputRef) zesuBugApplies zesuEquivalent.
Admitted.

Print Assumptions zesuCompliance.
