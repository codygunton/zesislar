Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuSsz.Export.DecodeTermination.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

(** Compose the completed main prefix and endpoint suffix through the named
    decoder termination hypothesis.  This lemma does not use decoder traces. *)
Lemma zesu_run_through_decode_termination
    (program : gmap addr isla_trace)
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (initial : spec) (emitted before : list seq_label) (args : DecodeBoundaryArgs)
    (instructions : nat) (start boundary : seq_local_state)
    (memory decoderMemory : seq_global_state)
    (terminal : list seq_label -> seq_local_state -> seq_global_state -> Prop)
    (decodeTerminates : decodeTerminationHypothesis program) :
  CompletedInstructionRun instructions start memory before boundary decoderMemory ->
  physicalMainDecodeEntry program decodeTail successExitTail initial
    (emitted ++ before) args boundary decoderMemory ->
  (forall decoderLabels outcome returned returnedMemory,
    physicalMainDecodeExit program decodeTail successExitTail initial
      ((emitted ++ before) ++ decoderLabels) args outcome returned returnedMemory ->
    exists count after finish finalMemory,
      CompletedInstructionRun count returned returnedMemory after finish finalMemory /\
      terminal (((emitted ++ before) ++ decoderLabels) ++ after) finish finalMemory) ->
  exists steps labels finish finalMemory,
    @nsteps isla_lang steps ([start], memory) labels ([finish], finalMemory) /\
    terminal (emitted ++ labels) finish finalMemory.
Proof.
  intros Hbefore Hentry Hcontinue.
  eapply (@completed_run_through_decoder
    (DecodeBoundaryOutcome WriteSuccessObservation)
    (fun prefix localState globalState =>
      physicalMainDecodeEntry program decodeTail successExitTail initial
        prefix args localState globalState)
    (fun prefix outcome localState globalState =>
      physicalMainDecodeExit program decodeTail successExitTail initial
        prefix args outcome localState globalState)
    emitted before instructions start boundary memory decoderMemory terminal).
  - intros prefix localState globalState Hentry'.
    exact (decodeTerminates decodeTail successExitTail initial prefix args
      localState globalState Hentry').
  - exact Hbefore.
  - exact Hentry.
  - exact Hcontinue.
Qed.

Print Assumptions zesu_run_through_decode_termination.
