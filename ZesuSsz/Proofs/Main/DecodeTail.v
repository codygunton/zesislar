Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.

Definition mainWriterArgs (args : DecodeBoundaryArgs)
    (observation : WriteSuccessObservation) : WriteSuccessArgs WriteSuccessObservation := {|
  successReturnAddress := 0x14d10;
  successStackPointer := decodeStackPointer args;
  successDecodedAddress := (decodeStackPointer args + 32)%Z;
  successDecoded := observation;
  successInputSize := length (decodeInput args)
|}.

Definition mainDecodeUnionTail
    (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
    (successExitTail failureExitTail : DecodeBoundaryArgs -> spec)
    (args : DecodeBoundaryArgs) : spec :=
  fun labels => exists outcome, allows args outcome /\
    match outcome with
    | DecodeBoundarySuccess observation =>
        exists witness : writeSuccessNativeWitness WriteSuccessObservation,
        writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness /\
        writeSuccessTraceTail witness = successExitTail args /\
        writeSuccessNativeTailEvents witness labels
    | DecodeBoundaryFailure =>
        writeOutputEvents (BV 64 0x177c8) (BV 64 6)
          failureMemory (failureExitTail args) labels
    end.

Lemma main_success_tail_subset allows successExitTail failureExitTail args observation witness :
  allows args (DecodeBoundarySuccess observation) ->
  writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness ->
  writeSuccessTraceTail witness = successExitTail args ->
  writeSuccessNativeTailEvents witness ⊆
    mainDecodeUnionTail allows successExitTail failureExitTail args.
Proof.
  intros Hallowed HwellFormed Htail labels Hlabels.
  exists (DecodeBoundarySuccess observation). split; first assumption.
  exists witness. auto.
Qed.

Lemma main_failure_tail_subset allows successExitTail failureExitTail args :
  allows args DecodeBoundaryFailure ->
  writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory (failureExitTail args) ⊆
    mainDecodeUnionTail allows successExitTail failureExitTail args.
Proof.
  intros Hallowed labels Hlabels. exists DecodeBoundaryFailure. auto.
Qed.

Lemma main_success_trace_select `{!islaG Sigma} `{!threadG}
    allows successExitTail failureExitTail args observation witness :
  allows args (DecodeBoundarySuccess observation) ->
  writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness ->
  writeSuccessTraceTail witness = successExitTail args ->
  spec_trace (mainDecodeUnionTail allows successExitTail failureExitTail args) -∗
  spec_trace (writeSuccessNativeTailEvents witness).
Proof.
  intros Hallowed HwellFormed Htail. iIntros "Hspec".
  iApply (spec_trace_mono with "Hspec").
  exact (main_success_tail_subset _ _ _ _ _ _ Hallowed HwellFormed Htail).
Qed.

Lemma main_failure_trace_select `{!islaG Sigma} `{!threadG}
    allows successExitTail failureExitTail args :
  allows args DecodeBoundaryFailure ->
  spec_trace (mainDecodeUnionTail allows successExitTail failureExitTail args) -∗
  spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory (failureExitTail args)).
Proof.
  intros Hallowed. iIntros "Hspec". iApply (spec_trace_mono with "Hspec").
  exact (main_failure_tail_subset _ _ _ _ Hallowed).
Qed.
Print Assumptions main_success_tail_subset.
Print Assumptions main_failure_tail_subset.
Print Assumptions main_success_trace_select.
Print Assumptions main_failure_trace_select.
