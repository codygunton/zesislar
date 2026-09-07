From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import IslaTraces.write_success_07.a15d20.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsOccurrence15d1cFirst state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d1c =
    Some (count_occ Z.eq_dec
      (firstn (342 + 8) writeSuccessWithdrawalsIterationPcs) 0x15d1c).
Proof.
  intros Hx1. unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx1. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsOccurrence15d20First state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d20 =
    Some (count_occ Z.eq_dec
      (firstn (342 + 9) writeSuccessWithdrawalsIterationPcs) 0x15d20).
Proof.
  intros Hx1. unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx1. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawals15d1cRankDecreases regs global log remaining
    (sp : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess15d1cAfter regs global sp, log) <
    rank_15694 (writeSuccess15d1cBefore regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d1cBefore regs global, log) = Some 0x15d1c.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d1cBefore,
      writeSuccess15d1cLocal. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d1cAfter regs global sp, log) = Some 0x15d20.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d1cAfter,
      writeSuccess15d1cLocal, writeSuccess15d1cRegs. cbn.
    rewrite lookup_insert writeSuccess15d1cNextPcExact. reflexivity. }
  have Hx1Before :
      (writeSuccess15d1cBefore regs global).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold writeSuccess15d1cBefore, writeSuccess15d1cLocal. cbn. exact Hx1. }
  have Hx9Before :
      (writeSuccess15d1cBefore regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess15d1cBefore, writeSuccess15d1cLocal. cbn. exact Hx9. }
  have Hx1After : (writeSuccess15d1cAfter regs global sp).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold writeSuccess15d1cAfter, writeSuccess15d1cLocal. cbn.
    rewrite writeSuccess15d1cRegsLookupOther; try discriminate. exact Hx1. }
  have Hx9After : (writeSuccess15d1cAfter regs global sp).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess15d1cAfter, writeSuccess15d1cLocal. cbn.
    rewrite writeSuccess15d1cRegsLookupOther; try discriminate. exact Hx9. }
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d1cBefore regs global, log) remaining 8 0x15d1c
    ltac:(reflexivity) HpcBefore
    (writeSuccessWithdrawalsOccurrence15d1cFirst
      (writeSuccess15d1cBefore regs global, log) Hx1Before) Hx9Before Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate)).
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex
    (writeSuccess15d1cAfter regs global sp, log) remaining 9 0x15d20
    ltac:(reflexivity) HpcAfter
    (writeSuccessWithdrawalsOccurrence15d20First
      (writeSuccess15d1cAfter regs global sp, log) Hx1After) Hx9After Hrange
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate)). lia.
Qed.

Lemma writeSuccess15d1cRegsDomFirst regs (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x10" = Some oldX10 ->
  dom (writeSuccess15d1cRegs regs sp) = dom regs.
Proof.
  intros Hpc Hx10. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx10.
  unfold writeSuccess15d1cRegs. rewrite !dom_insert_L. set_solver.
Qed.

Lemma writeSuccessWithdrawalsSegment15d1cFirstExistsAndDecreases
    regs global log remaining (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  writeSuccessTraceAssumptions (writeSuccess15d1cBefore regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess15d1cBefore regs global) observations after /\
    after = writeSuccess15d1cAfter regs global sp /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) < rank_15694 (writeSuccess15d1cBefore regs global, log).
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess15d1cObservations regs global sp),
    (writeSuccess15d1cAfter regs global sp). split.
  - exact (proj1 (segment_15d1c regs global sp oldX10 Hpc Hx2 Hx10
      Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess15d1cAfter, writeSuccess15d1cLocal. cbn.
      eapply writeSuccess15d1cRegsDomFirst; eassumption.
    + eapply writeSuccessWithdrawals15d1cRankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15d1cFirstDecreases
    regs global log remaining (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  writeSuccessTraceAssumptions (writeSuccess15d1cBefore regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess15d1cBefore regs global) observations after ->
  after = writeSuccess15d1cAfter regs global sp /\
  observations = writeSuccess15d1cObservations regs global sp /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) < rank_15694 (writeSuccess15d1cBefore regs global, log).
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_15d1c_covered regs global sp oldX10 observations after
    Hpc Hx2 Hx10 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobs].
  subst after. split; first reflexivity. split; first exact Hobs. split.
  - unfold writeSuccess15d1cAfter, writeSuccess15d1cLocal. cbn.
    eapply writeSuccess15d1cRegsDomFirst; eassumption.
  - eapply writeSuccessWithdrawals15d1cRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsOccurrence15d1cFirst.
Print Assumptions writeSuccessWithdrawalsOccurrence15d20First.
Print Assumptions writeSuccessWithdrawals15d1cRankDecreases.
Print Assumptions writeSuccess15d1cRegsDomFirst.
Print Assumptions writeSuccessWithdrawalsSegment15d1cFirstExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15d1cFirstDecreases.
