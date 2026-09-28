Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.GuardedTracePrefix.
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
Require Import ZesuSsz.Automation.Switches.SpecTail.
Lemma tf2_boolean_switch_zero (args : WriteSuccessArgs Decoded)
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
  time "generic Boolean C1" zesu_close_spec_tail_if_enabled.
  iFrame.
Qed.
Lemma tf2_boolean_switch_one (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (pc : Z) (continuation : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness -∗
  instr_pre pc continuation -∗
  (∃ x : spec *ₗ (),
    ⌜writeOutputEvents (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 1)) x.1ₗ
      ⊆ writeSuccessExactTailFirstBranchEvents witness⌝ ∗
    writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗
    instr_pre pc continuation ∗ True).
Proof.
  intros Hguard. iIntros "Hframe Hreturn".
  time "generic Boolean C1 one" zesu_close_spec_tail_if_enabled.
  iFrame.
Qed.
Lemma tf2_boolean_unreturned_bundle (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (pc : Z) (continuation : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness -∗
  (∃ x : spec *ₗ (),
    ⌜writeOutputEvents (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 0)) x.1ₗ
      ⊆ writeSuccessExactTailFirstBranchEvents witness⌝ ∗
    writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ True).
Proof.
  intros Hguard. iIntros "Hframe".
  Fail timeout 2 zesu_registered_trace_tail.
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

Lemma tf2_boolean_prefix_used (args : WriteSuccessArgs Decoded)
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
  pose proof (I : ZesuTracePrefixUsed (writeSuccessExactTailFirstBranchEvents witness)) as Hused.
  Fail timeout 2 zesu_registered_trace_tail.
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
Print Assumptions tf2_boolean_switch_zero.
Print Assumptions tf2_boolean_switch_one.
Print Assumptions tf2_boolean_unreturned_bundle.
Print Assumptions tf2_boolean_prefix_used.
