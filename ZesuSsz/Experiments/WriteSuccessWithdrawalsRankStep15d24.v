From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d24.
Require Import IslaTraces.write_success_07.a15d28.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsOccurrence15d24First state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d24 =
    Some (count_occ Z.eq_dec
      (firstn (342 + 10) writeSuccessWithdrawalsIterationPcs) 0x15d24).
Proof. intros H. unfold writeSuccessWithdrawalsSelectedOccurrence,
  writeSuccessWithdrawalsRegisterUnsigned. rewrite H. vm_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawalsOccurrence15d28First state :
  writeSuccessWithdrawalsSavedReturn state = Some 0x156b4 ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d28 =
    Some (count_occ Z.eq_dec
      (firstn (342 + 11) writeSuccessWithdrawalsIterationPcs) 0x15d28).
Proof. intros H. unfold writeSuccessWithdrawalsSelectedOccurrence.
  rewrite H. vm_compute. reflexivity. Qed.

Lemma writeSuccess15d24PreservesSavedReturn regs global log :
  writeSuccessWithdrawalsSavedReturn
    (writeSuccess15d24After regs global, log) =
  writeSuccessWithdrawalsSavedReturn
    (writeSuccess15d24Before regs global, log).
Proof.
  unfold writeSuccessWithdrawalsSavedReturn,
    writeSuccessWithdrawalsRegisterUnsigned, writeSuccess15d24After,
    writeSuccess15d24Before, writeSuccess15694Local. cbn.
  rewrite writeSuccess15d24RegsLookupOther; try discriminate. reflexivity.
Qed.

Lemma writeSuccessWithdrawals15d24RankDecreases regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  writeSuccessWithdrawalsSavedReturn
    (writeSuccess15d24Before regs global, log) = Some 0x156b4 ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess15d24After regs global, log) <
    rank_15694 (writeSuccess15d24Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hsaved Hrange.
  have HpcB : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d24Before regs global, log) = Some 0x15d24.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d24Before,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcA : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d24After regs global, log) = Some 0x15d28.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d24After,
      writeSuccess15694Local, writeSuccess15d24Regs. cbn.
    rewrite lookup_insert writeSuccess15d24NextPcExact. reflexivity. }
  have Hx1B : (writeSuccess15d24Before regs global).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)) by exact Hx1.
  have Hx9B : (writeSuccess15d24Before regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by exact Hx9.
  have Hx9A : (writeSuccess15d24After regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess15d24After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15d24RegsLookupOther; try discriminate. exact Hx9. }
  have HsavedA : writeSuccessWithdrawalsSavedReturn
      (writeSuccess15d24After regs global, log) = Some 0x156b4.
  { rewrite writeSuccess15d24PreservesSavedReturn. exact Hsaved. }
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d24Before regs global, log) remaining 10 0x15d24
    ltac:(reflexivity) HpcB
    (writeSuccessWithdrawalsOccurrence15d24First
      (writeSuccess15d24Before regs global, log) Hx1B) Hx9B Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d24After regs global, log) remaining 11 0x15d28
    ltac:(reflexivity) HpcA
    (writeSuccessWithdrawalsOccurrence15d28First
      (writeSuccess15d24After regs global, log) HsavedA) Hx9A Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment15d24FirstExistsAndDecreases
    regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  writeSuccessTraceAssumptions (writeSuccess15d24Before regs global) ->
  writeSuccessWithdrawalsSavedReturn
    (writeSuccess15d24Before regs global, log) = Some 0x156b4 ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess15d24Before regs global) observations after /\
    after = writeSuccess15d24After regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) < rank_15694 (writeSuccess15d24Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hsaved Hrange.
  exists (writeSuccess15d24Observations regs global),
    (writeSuccess15d24After regs global). split.
  - exact (proj1 (segment_15d24 regs global (RVal_Bits (Z_to_bv 64 0x156b4))
      Hpc Hx1 Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess15d24After, writeSuccess15694Local. cbn.
      eapply writeSuccess15d24RegsDom; eassumption.
    + eapply writeSuccessWithdrawals15d24RankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15d24FirstDecreases
    regs global log remaining observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  writeSuccessTraceAssumptions (writeSuccess15d24Before regs global) ->
  writeSuccessWithdrawalsSavedReturn
    (writeSuccess15d24Before regs global, log) = Some 0x156b4 ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess15d24Before regs global) observations after ->
  after = writeSuccess15d24After regs global /\
  observations = writeSuccess15d24Observations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) < rank_15694 (writeSuccess15d24Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hsaved Hrange Hsegment.
  destruct (segment_15d24_covered regs global (RVal_Bits (Z_to_bv 64 0x156b4))
    observations after Hpc Hx1 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobs].
  subst after. split; first reflexivity. split; first exact Hobs. split.
  - unfold writeSuccess15d24After, writeSuccess15694Local. cbn.
    eapply writeSuccess15d24RegsDom; eassumption.
  - eapply writeSuccessWithdrawals15d24RankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsOccurrence15d24First.
Print Assumptions writeSuccessWithdrawalsOccurrence15d28First.
Print Assumptions writeSuccess15d24PreservesSavedReturn.
Print Assumptions writeSuccessWithdrawals15d24RankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment15d24FirstExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15d24FirstDecreases.
