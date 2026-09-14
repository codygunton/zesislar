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
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
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

(** Phase 2.3 defines these projections from snapshot labels. *)
Definition zesuOutcomeOfTrace (_ : list seq_label) : option DecodeOutcome := None.
Definition zesuInputOfTrace (_ : list seq_label) : option ByteString := None.

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
  successDecodedAddress := decodeInputAddress args;
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
