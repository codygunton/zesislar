Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Compliance.ObservationBridge.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.Main.Main.
Require Import ZesuSsz.Proofs.Main.SnapshotInput.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.WholeResources.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.Contract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.

Import ListNotations.

Definition mainContractInputOfTrace := mainInputOfTrace.

Fixpoint mainOutputOfTrace (labels : list seq_label) : option ByteString :=
  match labels with
  | [] => None
  | label :: rest =>
      match label, rest with
      | SWriteMem address data _,
          SWriteMem sizeAddress size snapshot :: _ =>
          if executor_bits_eqb address
              (BV 64 (machineOutputAddress defaultMap)) &&
             executor_bits_eqb sizeAddress
              (BV 64 (machineOutputSizeAddress defaultMap)) then
            (List.map bv_unsigned) <$>
              read_mem_list snapshot.(snap_mem) (bvn_unsigned data)
                (Z.to_N (bvn_unsigned size))
          else mainOutputOfTrace rest
      | _, _ => mainOutputOfTrace rest
      end
  end.

Definition mainOutcomeOfBytes (bytes : ByteString) : option DecodeOutcome :=
  if decide (bytes = failureObservation) then Some DecodeFailure
  else
    match writeSuccessDecodeObservation bytes with
    | Some observation =>
        Some (DecodeSuccess (observationToStatelessInput observation))
    | None => None
    end.

Definition mainContractOutcomeOfTrace (labels : list seq_label) :
    option DecodeOutcome :=
  match mainOutputOfTrace labels with
  | Some output => mainOutcomeOfBytes output
  | None => None
  end.

Lemma main_output_of_trace_prefix data size firstSnapshot writeSnapshot
    labels payload :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
      (Z.to_N (bvn_unsigned size)) = Some payload ->
  mainOutputOfTrace
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) =
    Some (List.map bv_unsigned payload).
Proof.
  intros Hpayload. cbn [mainOutputOfTrace executor_bits_eqb].
  rewrite Hpayload. reflexivity.
Qed.

Lemma main_output_of_trace_events data size payload tail firstSnapshot
    writeSnapshot labels :
  writeOutputEvents data size payload tail
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) ->
  mainOutputOfTrace
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) =
    Some (List.map bv_unsigned payload).
Proof.
  intros Hevents. apply main_output_of_trace_prefix.
  eapply write_output_events_payload. exact Hevents.
Qed.

Lemma main_contract_trace_input_bytes labels input :
  mainContractInputOfTrace labels = Some input ->
  Forall (fun value => (0 <= value < 256)%Z) input.
Proof. exact (main_trace_input_bytes labels input). Qed.

Lemma main_contract_outcome_of_trace_prefix data size firstSnapshot
    writeSnapshot labels payload outcome :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
      (Z.to_N (bvn_unsigned size)) = Some payload ->
  mainOutcomeOfBytes (List.map bv_unsigned payload) = Some outcome ->
  mainContractOutcomeOfTrace
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) = Some outcome.
Proof.
  intros Hpayload Houtcome. rewrite /mainContractOutcomeOfTrace.
  erewrite main_output_of_trace_prefix; [exact Houtcome | exact Hpayload].
Qed.

Lemma main_outcome_of_failure :
  mainOutcomeOfBytes failureObservation = Some DecodeFailure.
Proof.
  unfold mainOutcomeOfBytes.
  destruct (decide (failureObservation = failureObservation));
    [reflexivity | contradiction].
Qed.

Lemma main_outcome_of_success observation :
  writeSuccessObservationValid observation ->
  mainOutcomeOfBytes (writeSuccessEncodeObservation observation) =
    Some (DecodeSuccess (observationToStatelessInput observation)).
Proof.
  intros Hvalid. unfold mainOutcomeOfBytes.
  destruct (decide (writeSuccessEncodeObservation observation = failureObservation))
    as [Heq | Hneq].
  - unfold writeSuccessEncodeObservation, failureObservation in Heq. discriminate.
  - rewrite writeSuccessObservationDecodeEncode; [reflexivity | exact Hvalid].
Qed.

Lemma main_contract_outcome_of_trace_failure firstSnapshot writeSnapshot
    labels tail :
  writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory tail
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) (BV 64 0x177c8)
         firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) (BV 64 6)
         writeSnapshot :: labels) ->
  mainContractOutcomeOfTrace
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) (BV 64 0x177c8)
         firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) (BV 64 6)
         writeSnapshot :: labels) = Some DecodeFailure.
Proof.
  intros Hevents. rewrite /mainContractOutcomeOfTrace.
  erewrite main_output_of_trace_events; [| exact Hevents].
  change (mainOutcomeOfBytes failureObservation = Some DecodeFailure).
  exact main_outcome_of_failure.
Qed.

Lemma main_contract_outcome_of_trace_success data size payload firstSnapshot
    writeSnapshot labels tail observation :
  writeOutputEvents data size payload tail
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) ->
  List.map bv_unsigned payload = writeSuccessEncodeObservation observation ->
  writeSuccessObservationValid observation ->
  mainContractOutcomeOfTrace
      (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
       SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
       labels) =
    Some (DecodeSuccess (observationToStatelessInput observation)).
Proof.
  intros Hevents Hpayload Hvalid. rewrite /mainContractOutcomeOfTrace.
  erewrite main_output_of_trace_events; [| exact Hevents].
  rewrite Hpayload. apply main_outcome_of_success. exact Hvalid.
Qed.

Theorem main_whole_from_fixed_tail_contract
    (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
    (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation)
    (tail : spec)
    (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64)
    (decodeOk : IslarisContractCorrect 0x12168 0x14cfc
      (mainConcreteDecodeModel allows
        (mainDecodeUnionTail allows
          (fun _ => scons
            (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
          (fun _ => scons
            (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
        (fun _ => scons
          (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)))
    (writeOk : writeSuccessFixedTailContractTarget writeAllows outputRelation
      (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
      (fun _ nextPc => nextPc = 0x14d10)) :
  IslarisContractCorrect 0x14cb0 0x101d0
    (mainWholeModel allows writeAllows outputRelation tail
      a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13).
Proof.
  apply main_whole_correct; first exact decodeOk.
  exact writeOk.
Qed.

Print Assumptions main_output_of_trace_prefix.
Print Assumptions main_output_of_trace_events.
Print Assumptions main_contract_trace_input_bytes.
Print Assumptions main_contract_outcome_of_trace_prefix.
Print Assumptions main_outcome_of_failure.
Print Assumptions main_outcome_of_success.
Print Assumptions main_contract_outcome_of_trace_failure.
Print Assumptions main_contract_outcome_of_trace_success.
Print Assumptions main_whole_from_fixed_tail_contract.
