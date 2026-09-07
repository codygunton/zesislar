From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import IslaTraces.write_success_07.a15d14.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep156b0.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPhase15d14First state :
  writeSuccessWithdrawalsConcretePc state = Some 0x15d14 ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 62%nat.
Proof.
  intros Hpc Hx1. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx1.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_15d14_first state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x15d14 ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 62)%nat.
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase15d14First state Hpc Hx1.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn. rewrite Hphase.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawals15d10RankDecreases regs global log remaining
    (sp : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess15d10After regs global sp, log) <
    rank_15694 (writeSuccess15d10Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d10Before regs global, log) = Some 0x15d10.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d10Before,
      writeSuccess15d10Local. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess15d10After regs global sp, log) = Some 0x15d14.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d10After,
      writeSuccess15d10Local, writeSuccess15d10Regs. cbn.
    rewrite lookup_insert writeSuccess15d10NextPcExact. reflexivity. }
  have Hx1After : (writeSuccess15d10After regs global sp).1.(seq_regs) !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
    rewrite writeSuccess15d10RegsLookupOther; try discriminate. exact Hx1. }
  have Hx9After : (writeSuccess15d10After regs global sp).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
    rewrite writeSuccess15d10RegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_15d10_first (writeSuccess15d10Before regs global, log)
    remaining HpcBefore Hx1 Hx9 Hrange).
  rewrite (rank_15694_at_15d14_first (writeSuccess15d10After regs global sp, log)
    remaining HpcAfter Hx1After Hx9After Hrange). lia.
Qed.

Lemma writeSuccess15d10RegsDomFirst regs (sp : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  dom (writeSuccess15d10Regs regs sp) = dom regs.
Proof.
  intros Hpc Hx2. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx2.
  unfold writeSuccess15d10Regs. rewrite !dom_insert_L. set_solver.
Qed.

Lemma writeSuccessWithdrawalsSegment15d10FirstExistsAndDecreases
    regs global log remaining (sp : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  writeSuccessTraceAssumptions (writeSuccess15d10Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess15d10Before regs global) observations after /\
    after = writeSuccess15d10After regs global sp /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) < rank_15694 (writeSuccess15d10Before regs global, log).
Proof.
  intros Hpc Hx1 Hx2 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess15d10Observations regs global sp),
    (writeSuccess15d10After regs global sp). split.
  - exact (proj1 (segment_15d10 regs global sp (RVal_Bits sp) Hpc Hx2 Hx2
      Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
      apply writeSuccess15d10RegsDomFirst; assumption.
    + eapply writeSuccessWithdrawals15d10RankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15d10FirstDecreases
    regs global log remaining (sp : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  writeSuccessTraceAssumptions (writeSuccess15d10Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess15d10Before regs global) observations after ->
  after = writeSuccess15d10After regs global sp /\
  observations = writeSuccess15d10Observations regs global sp /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) < rank_15694 (writeSuccess15d10Before regs global, log).
Proof.
  intros Hpc Hx1 Hx2 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_15d10_covered regs global sp (RVal_Bits sp)
    observations after Hpc Hx2 Hx2 Hcode Hnext Hassumptions Hsegment)
    as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
    apply writeSuccess15d10RegsDomFirst; assumption.
  - eapply writeSuccessWithdrawals15d10RankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase15d14First.
Print Assumptions rank_15694_at_15d14_first.
Print Assumptions writeSuccessWithdrawals15d10RankDecreases.
Print Assumptions writeSuccess15d10RegsDomFirst.
Print Assumptions writeSuccessWithdrawalsSegment15d10FirstExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15d10FirstDecreases.
