From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedPositions.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderIntegerSelected state pc (returnAddress : bv 64) :
  In pc [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20; 0x15d24;
    0x15d30; 0x15d34] ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hx1.
  unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn in Hpc. decompose [or] Hpc; try contradiction; subst pc; cbn; rewrite Hx1; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntegerSavedSelected state pc (returnAddress : bv 64) :
  (pc = 0x15d28 \/ pc = 0x15d2c) ->
  writeSuccessWithdrawalsSavedReturn state = Some (bv_unsigned returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hsaved; destruct Hpc as [Hpc|Hpc]; subst pc; unfold writeSuccessWithdrawalsSelectedOccurrence;
    rewrite Hsaved; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderOutputSelected state pc (returnAddress : bv 64) :
  In pc [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0] ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  writeSuccessWithdrawalsSavedReturn state = Some (bv_unsigned returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsOutputOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hx1 Hsaved.
  unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn in Hpc. decompose [or] Hpc; try contradiction; subst pc;
    rewrite Hx1; cbn; rewrite Hsaved; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsActualPositionSuccessor segments states position
    observations state fallback :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  nth_error segments position = Some observations ->
  nth_error states (S position) = Some state ->
  exists labels,
    List.last observations fallback =
      {| microLabels := labels; microAfter := state.1 |}.
Proof.
  intros Hedges Hobservations Hstate.
  have Hposition : (position < length segments)%nat.
  { have Hlength := writeSuccessWithdrawalsPositionEdgesLength segments states
      Hedges.
    apply nth_error_Some. intros Hnone. rewrite Hnone in Hobservations.
    discriminate. }
  destruct (writeSuccessWithdrawalsPositionEdgesNth segments states position
    Hedges Hposition) as
    (actualObservations & before & after & Hactual & _ & Hafter & Hone).
  rewrite Hobservations in Hactual. injection Hactual as ->.
  rewrite Hstate in Hafter. injection Hafter as ->.
  apply (writeSuccessWithdrawalsRecordedEdgeLast _ _ _ fallback) in Hone.
  exact Hone.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntegerSelected.
Print Assumptions writeSuccessWithdrawalsEncoderIntegerSavedSelected.
Print Assumptions writeSuccessWithdrawalsEncoderOutputSelected.
Print Assumptions writeSuccessWithdrawalsActualPositionSuccessor.
