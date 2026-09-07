From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep156ac.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPhase15d10First state :
  writeSuccessWithdrawalsConcretePc state = Some 0x15d10 ->
  state.1.1.(seq_regs) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 63%nat.
Proof.
  intros Hpc Hx1. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx1.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_15d10_first state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x15d10 ->
  state.1.1.(seq_regs) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 63)%nat.
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase15d10First state Hpc Hx1.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn. rewrite Hphase.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawals156b0RankDecreases regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess156b0After regs global, log) <
    rank_15694 (writeSuccess156b0Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess156b0Before regs global, log) = Some 0x156b0.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess156b0Before,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess156b0After regs global, log) = Some 0x15d10.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess156b0After,
      writeSuccess15694Local, writeSuccess156b0Regs. cbn.
    rewrite lookup_insert. destruct writeSuccess156b0ValuesExact as (_&_&_&H).
    rewrite H. reflexivity. }
  have Hx1After : (writeSuccess156b0After regs global).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold writeSuccess156b0After, writeSuccess15694Local,
      writeSuccess156b0Regs. cbn. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. destruct writeSuccess156b0ValuesExact as (_&H&_).
    rewrite H. reflexivity. }
  have Hx9After : (writeSuccess156b0After regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess156b0After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156b0RegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_156b0 (writeSuccess156b0Before regs global, log)
    remaining HpcBefore Hx9 Hrange).
  rewrite (rank_15694_at_15d10_first (writeSuccess156b0After regs global, log)
    remaining HpcAfter Hx1After Hx9After Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsSegment156b0ExistsAndDecreases regs global log
    remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  writeSuccessTraceAssumptions (writeSuccess156b0Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess156b0Before regs global) observations after /\
    after = writeSuccess156b0After regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) < rank_15694 (writeSuccess156b0Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess156b0Observations regs global),
    (writeSuccess156b0After regs global). split.
  - exact (proj1 (segment_156b0 regs global Hpc Hx1 Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess156b0After, writeSuccess15694Local. cbn.
      apply writeSuccess156b0RegsDom; assumption.
    + eapply writeSuccessWithdrawals156b0RankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment156b0Decreases regs global log
    remaining observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  writeSuccessTraceAssumptions (writeSuccess156b0Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess156b0Before regs global) observations after ->
  after = writeSuccess156b0After regs global /\
  observations = writeSuccess156b0Observations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) < rank_15694 (writeSuccess156b0Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_156b0_covered regs global observations after Hpc Hx1
    Hcode Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess156b0After, writeSuccess15694Local. cbn.
    apply writeSuccess156b0RegsDom; assumption.
  - eapply writeSuccessWithdrawals156b0RankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase15d10First.
Print Assumptions rank_15694_at_15d10_first.
Print Assumptions writeSuccessWithdrawals156b0RankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment156b0ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment156b0Decreases.
