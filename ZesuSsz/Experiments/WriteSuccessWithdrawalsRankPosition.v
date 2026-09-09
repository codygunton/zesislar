From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankAdjacent.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsPositionState
    (remaining position : nat) (state : WriteSuccessWithdrawalsConcreteState) :
    Prop :=
  exists pc,
    nth_error writeSuccessWithdrawalsIterationPcs position = Some pc /\
    writeSuccessWithdrawalsConcretePc state = Some pc /\
    writeSuccessWithdrawalsSelectedOccurrence state pc =
      Some (count_occ Z.eq_dec
        (firstn position writeSuccessWithdrawalsIterationPcs) pc) /\
    state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
    pc <> 0x156e4 /\ pc <> 0x156e8 /\ pc <> 0x1568c /\ pc <> 0x15690 /\
    (Z.of_nat (S remaining) < 2 ^ 64)%Z.

Definition writeSuccessWithdrawalsTerminalPositionState
    (remaining : nat) (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  writeSuccessWithdrawalsConcretePc state = Some 0x156e4 /\
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) /\
  (Z.of_nat remaining < 2 ^ 64)%Z.

Definition writeSuccessWithdrawalsSegmentEquation
    (remaining position : nat) (before after : WriteSuccessWithdrawalsConcreteState) :
    Prop :=
  ((position < 408)%nat /\
    writeSuccessWithdrawalsPositionState remaining position before /\
    writeSuccessWithdrawalsPositionState remaining (S position) after) \/
  (position = 408%nat /\
    writeSuccessWithdrawalsPositionState remaining 408 before /\
    writeSuccessWithdrawalsTerminalPositionState remaining after) \/
  (position = 409%nat /\
    writeSuccessWithdrawalsTerminalPositionState remaining before /\
    writeSuccessWithdrawalsConcretePc after =
      Some (if remaining is O then 0x156e8 else 0x15694) /\
    after.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining)))).

Definition writeSuccessWithdrawalsOrdinaryPc (pc : Z) : bool :=
  (** Positions before the loop branch exclude all special rank cases. *)
  negb (Z.eqb pc 0x156e4) && negb (Z.eqb pc 0x156e8) &&
  negb (Z.eqb pc 0x1568c) && negb (Z.eqb pc 0x15690).

Lemma writeSuccessWithdrawalsOrdinaryPositionsChecked :
  forallb
    (fun position =>
      match nth_error writeSuccessWithdrawalsIterationPcs position with
      | Some pc => writeSuccessWithdrawalsOrdinaryPc pc
      | None => false
      end)
    (seq 0 409) = true.
Proof. native_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawalsOrdinaryPosition position pc :
  (position < 409)%nat ->
  nth_error writeSuccessWithdrawalsIterationPcs position = Some pc ->
  pc <> 0x156e4 /\ pc <> 0x156e8 /\ pc <> 0x1568c /\ pc <> 0x15690.
Proof.
  intros Hposition Hnth.
  have Hin : In position (seq 0 409).
  { apply in_seq. lia. }
  have Hchecked := writeSuccessWithdrawalsOrdinaryPositionsChecked.
  apply forallb_forall with (x := position) in Hchecked; last exact Hin.
  rewrite Hnth in Hchecked.
  unfold writeSuccessWithdrawalsOrdinaryPc in Hchecked.
  repeat rewrite Bool.andb_true_iff in Hchecked.
  repeat rewrite Bool.negb_true_iff in Hchecked.
  repeat rewrite Z.eqb_neq in Hchecked.
  tauto.
Qed.

Lemma writeSuccessWithdrawalsRankAtPosition remaining position state :
  writeSuccessWithdrawalsPositionState remaining position state ->
  rank_15694 state = (410 * remaining + (410 - position))%nat.
Proof.
  intros (pc & Hnth & Hpc & Hocc & Hx9 & HnotE4 & HnotE8 & Hnot8c &
    Hnot90 & Hrange).
  have Hphase : writeSuccessWithdrawalsPhaseRemaining state =
      (410 - position)%nat.
  { rewrite (writeSuccessWithdrawalsPhaseFromSelectedOccurrence state pc _
      Hpc Hocc).
    pose proof (writeSuccessOccurrenceRemainingAtIndex
      writeSuccessWithdrawalsIterationPcs position pc Hnth) as Hremaining.
    rewrite writeSuccessWithdrawalsIterationPcsLength in Hremaining.
    exact Hremaining. }
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn.
  assert (HE4 : Z.eqb pc 0x156e4 = false) by
    (apply Z.eqb_neq; exact HnotE4).
  assert (HE8 : Z.eqb pc 0x156e8 = false) by
    (apply Z.eqb_neq; exact HnotE8).
  assert (H8c : Z.eqb pc 0x1568c = false) by
    (apply Z.eqb_neq; exact Hnot8c).
  assert (H90 : Z.eqb pc 0x15690 = false) by
    (apply Z.eqb_neq; exact Hnot90).
  rewrite HE4 HE8 H8c H90.
  rewrite Hphase Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn in Hrange |- *. lia.
Qed.

Lemma writeSuccessWithdrawalsRankAtTerminalPosition remaining state :
  writeSuccessWithdrawalsTerminalPositionState remaining state ->
  rank_15694 state = (410 * remaining + 1)%nat.
Proof.
  intros (Hpc & Hx9 & Hrange).
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. lia.
  - unfold bv_modulus. cbn in Hrange |- *. lia.
Qed.

Theorem writeSuccessWithdrawalsRankAdjacentPosition
    remaining position before after :
  (position < 408)%nat ->
  writeSuccessWithdrawalsPositionState remaining position before ->
  writeSuccessWithdrawalsPositionState remaining (S position) after ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hposition Hbefore Hafter.
  rewrite (writeSuccessWithdrawalsRankAtPosition _ _ _ Hbefore).
  rewrite (writeSuccessWithdrawalsRankAtPosition _ _ _ Hafter).
  lia.
Qed.

Theorem writeSuccessWithdrawalsRankPosition408
    remaining before after :
  writeSuccessWithdrawalsPositionState remaining 408 before ->
  writeSuccessWithdrawalsTerminalPositionState remaining after ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hbefore Hafter.
  rewrite (writeSuccessWithdrawalsRankAtPosition _ _ _ Hbefore).
  rewrite (writeSuccessWithdrawalsRankAtTerminalPosition _ _ Hafter).
  lia.
Qed.

Theorem writeSuccessWithdrawalsRankPosition409FromTable
    remaining before after :
  writeSuccessWithdrawalsTerminalPositionState remaining before ->
  writeSuccessWithdrawalsConcretePc after =
    Some (if remaining is O then 0x156e8 else 0x15694) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  rank_15694 after < rank_15694 before.
Proof.
  intros (Hpc & Hx9 & Hrange) HafterPc HafterX9.
  eapply writeSuccessWithdrawalsRankPosition409; eassumption.
Qed.

Theorem writeSuccessWithdrawalsRankFromSegmentEquation
    remaining position before after :
  (position < 410)%nat ->
  writeSuccessWithdrawalsSegmentEquation remaining position before after ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hposition [Hordinary|[Hcount|Hterminal]].
  - destruct Hordinary as (HbeforePosition & Hbefore & Hafter).
    eapply writeSuccessWithdrawalsRankAdjacentPosition; eassumption.
  - destruct Hcount as (-> & Hbefore & Hafter).
    eapply writeSuccessWithdrawalsRankPosition408; eassumption.
  - destruct Hterminal as (-> & Hbefore & HafterPc & HafterX9).
    eapply writeSuccessWithdrawalsRankPosition409FromTable; eassumption.
Qed.

Definition writeSuccessWithdrawalsRankedEndpoints
    (remaining : nat) (states : list WriteSuccessWithdrawalsConcreteState) : Prop :=
  length states = 411%nat /\
  forall position before after,
    (position < 410)%nat ->
    nth_error states position = Some before ->
    nth_error states (S position) = Some after ->
    writeSuccessWithdrawalsSegmentEquation remaining position before after.

Theorem writeSuccessWithdrawalsWholeTableRankDecreases remaining states :
  writeSuccessWithdrawalsRankedEndpoints remaining states ->
  forall position before after,
    (position < 410)%nat ->
    nth_error states position = Some before ->
    nth_error states (S position) = Some after ->
    rank_15694 after < rank_15694 before.
Proof.
  intros [_ Hequations] position before after Hposition Hbefore Hafter.
  apply (writeSuccessWithdrawalsRankFromSegmentEquation remaining position).
  - exact Hposition.
  - eapply Hequations; eassumption.
Qed.

Lemma writeSuccessWithdrawalsPositionExists position :
  (position < 410)%nat ->
  exists pc, nth_error writeSuccessWithdrawalsIterationPcs position = Some pc.
Proof.
  intros Hposition.
  destruct (nth_error writeSuccessWithdrawalsIterationPcs position) as [pc|]
    eqn:Hnth.
  - exists pc. reflexivity.
  - exfalso. apply nth_error_None in Hnth.
    rewrite writeSuccessWithdrawalsIterationPcsLength in Hnth. lia.
Qed.

Lemma writeSuccessWithdrawalsPosition409Pc :
  nth_error writeSuccessWithdrawalsIterationPcs 409 = Some 0x156e4.
Proof. reflexivity. Qed.

Print Assumptions writeSuccessWithdrawalsRankAtPosition.
Print Assumptions writeSuccessWithdrawalsOrdinaryPosition.
Print Assumptions writeSuccessWithdrawalsRankAtTerminalPosition.
Print Assumptions writeSuccessWithdrawalsRankAdjacentPosition.
Print Assumptions writeSuccessWithdrawalsRankPosition408.
Print Assumptions writeSuccessWithdrawalsRankPosition409FromTable.
Print Assumptions writeSuccessWithdrawalsRankFromSegmentEquation.
Print Assumptions writeSuccessWithdrawalsWholeTableRankDecreases.
Print Assumptions writeSuccessWithdrawalsPositionExists.
Print Assumptions writeSuccessWithdrawalsPosition409Pc.
