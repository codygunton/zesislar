Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessPostTransactionResources WriteSuccessExactBooleanSpec
  WriteSuccessExactTailBooleanTracePrefix.
Section tests.
Context `{!islaG Sigma} `{!threadG} {Decoded}
  `{!WriteSuccessMemoryRepresentation Decoded}.
Lemma tf2_boolean_switch_inactive (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (pc : Z) (continuation : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness -∗
  instr_pre pc continuation -∗
  (∃ x : spec *ₗ (),
    ⌜writeOutputEvents (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 0)) x.1ₗ
      ⊆ writeSuccessExactTailFirstBranchEvents witness⌝ ∗
    writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗
    instr_pre pc continuation ∗ True).
Proof.
  intros Hguard. iIntros "Hframe Hreturn".
  Fail zesu_close_spec_tail_if_enabled.
  iDestruct (tail_boolean_zero_trace_from_frame args witness Hguard with "Hframe") as "[%Hconnection Hframe]".
  iExists (writeSuccessExactTailAfterConditionalEvents witness, tt)ₗ.
  iSplit.
  - iPureIntro.
    have Haddr : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv =
      (writeSuccessFrameSp witness - BV 64 9)%bv.
    { unfold writeSuccessFrameSp. bv_solve. }
    rewrite Haddr Hconnection. reflexivity.
  - iFrame.
Qed.
End tests.
Print Assumptions tf2_boolean_switch_inactive.
