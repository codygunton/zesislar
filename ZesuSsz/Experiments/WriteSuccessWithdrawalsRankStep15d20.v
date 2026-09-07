From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d20.
Require Import IslaTraces.write_success_07.a15d24.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsOccurrence15d20First state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d20 =
    Some (count_occ Z.eq_dec
      (firstn (342 + 9) writeSuccessWithdrawalsIterationPcs) 0x15d20).
Proof. intros H. unfold writeSuccessWithdrawalsSelectedOccurrence,
  writeSuccessWithdrawalsRegisterUnsigned. rewrite H. vm_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawalsOccurrence15d24First state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d24 =
    Some (count_occ Z.eq_dec
      (firstn (342 + 10) writeSuccessWithdrawalsIterationPcs) 0x15d24).
Proof. intros H. unfold writeSuccessWithdrawalsSelectedOccurrence,
  writeSuccessWithdrawalsRegisterUnsigned. rewrite H. vm_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawals15d20RankDecreases regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess15d20After regs global, log) <
    rank_15694 (writeSuccess15d20Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have HpcB : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d20Before regs global, log) = Some 0x15d20.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d20Before,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcA : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d20After regs global, log) = Some 0x15d24.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d20After,
      writeSuccess15694Local, writeSuccess15d20Regs. cbn.
    rewrite lookup_insert writeSuccess15d20NextPcExact. reflexivity. }
  have Hx1B : (writeSuccess15d20Before regs global).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { exact Hx1. }
  have Hx9B : (writeSuccess15d20Before regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { exact Hx9. }
  have Hx1A : (writeSuccess15d20After regs global).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold writeSuccess15d20After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15d20RegsLookupOther; try discriminate. exact Hx1. }
  have Hx9A : (writeSuccess15d20After regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess15d20After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15d20RegsLookupOther; try discriminate. exact Hx9. }
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d20Before regs global, log) remaining 9 0x15d20
    ltac:(reflexivity) HpcB
    (writeSuccessWithdrawalsOccurrence15d20First
      (writeSuccess15d20Before regs global, log) Hx1B) Hx9B Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d20After regs global, log) remaining 10 0x15d24
    ltac:(reflexivity) HpcA
    (writeSuccessWithdrawalsOccurrence15d24First
      (writeSuccess15d20After regs global, log) Hx1A) Hx9A Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment15d20FirstExistsAndDecreases
    regs global log remaining oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x11" = Some oldX11 ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  writeSuccessTraceAssumptions (writeSuccess15d20Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess15d20Before regs global) observations after /\
    after = writeSuccess15d20After regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) < rank_15694 (writeSuccess15d20Before regs global, log).
Proof.
  intros Hpc Hx1 Hx11 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess15d20Observations regs global),
    (writeSuccess15d20After regs global). split.
  - exact (proj1 (segment_15d20 regs global oldX11 Hpc Hx11 Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess15d20After, writeSuccess15694Local. cbn.
      eapply writeSuccess15d20RegsDom; eassumption.
    + eapply writeSuccessWithdrawals15d20RankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15d20FirstDecreases
    regs global log remaining oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x11" = Some oldX11 ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  writeSuccessTraceAssumptions (writeSuccess15d20Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess15d20Before regs global) observations after ->
  after = writeSuccess15d20After regs global /\
  observations = writeSuccess15d20Observations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) < rank_15694 (writeSuccess15d20Before regs global, log).
Proof.
  intros Hpc Hx1 Hx11 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_15d20_covered regs global oldX11 observations after
    Hpc Hx11 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobs].
  subst after. split; first reflexivity. split; first exact Hobs. split.
  - unfold writeSuccess15d20After, writeSuccess15694Local. cbn.
    eapply writeSuccess15d20RegsDom; eassumption.
  - eapply writeSuccessWithdrawals15d20RankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsOccurrence15d20First.
Print Assumptions writeSuccessWithdrawalsOccurrence15d24First.
Print Assumptions writeSuccessWithdrawals15d20RankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment15d20FirstExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15d20FirstDecreases.
