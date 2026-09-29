Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessPostTransactionResources WriteSuccessOutputSemantic
  WriteSuccessObservation WriteSuccessExactBooleanSpec
  WriteSuccessExactTailBooleanTracePrefix.
Require Import ZesuSsz.Export.Snapshots.

Lemma exact_tail_absent_boolean_trace_handoff
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗
  spec_trace (writeSuccessExactTailFirstBranchEvents witness) ∗ P -∗
  spec_trace (writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv
    (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 0))
    (writeSuccessExactTailAfterConditionalEvents witness)) ∗
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ P.
Proof.
  intros Hzero. iIntros "(Hframe & Htrace & HP)".
  iDestruct (tail_boolean_zero_trace_from_frame args witness Hzero with "Hframe")
    as "[%Hprefix Hframe]".
  iEval (rewrite Hprefix) in "Htrace". iFrame.
Qed.
Print Assumptions exact_tail_absent_boolean_trace_handoff.

Lemma exact_tail_present_boolean_trace_handoff
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗
  spec_trace (writeSuccessExactTailFirstBranchEvents witness) ∗ P -∗
  ∃ payload : list (bv 8),
    spec_trace (writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv
      (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1))
      (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8))))
        (writeOutputEvents
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7)
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8)
          payload (writeSuccessExactTailAfterConditionalEvents witness)))) ∗
    writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ P.
Proof.
  intros Hpresent. iIntros "(Hframe & Htrace & HP)".
  iDestruct (tail_boolean_one_trace_from_frame args witness Hpresent with "Hframe")
    as "[%Hprefix Hframe]".
  destruct Hprefix as (payload & Hprefix). iExists payload.
  iEval (rewrite Hprefix) in "Htrace". iFrame.
Qed.
Print Assumptions exact_tail_present_boolean_trace_handoff.
