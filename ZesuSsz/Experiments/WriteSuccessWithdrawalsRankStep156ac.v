From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156acCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPhase156ac state :
  writeSuccessWithdrawalsConcretePc state = Some 0x156ac ->
  writeSuccessWithdrawalsPhaseRemaining state = 65%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPhase156b0 state :
  writeSuccessWithdrawalsConcretePc state = Some 0x156b0 ->
  writeSuccessWithdrawalsPhaseRemaining state = 64%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_156ac state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x156ac ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 65)%nat.
Proof.
  intros Hpc Hx9 Hrange. have Hphase := writeSuccessWithdrawalsPhase156ac state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn. rewrite Hphase.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_156b0 state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x156b0 ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 64)%nat.
Proof.
  intros Hpc Hx9 Hrange. have Hphase := writeSuccessWithdrawalsPhase156b0 state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn. rewrite Hphase.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawals156acRankDecreases regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess156acAfter regs global, log) <
    rank_15694 (writeSuccess156acBefore regs global, log).
Proof.
  intros Hpc Hx9 Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess156acBefore regs global, log) = Some 0x156ac.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess156acBefore,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess156acAfter regs global, log) = Some 0x156b0.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess156acAfter,
      writeSuccess15694Local, writeSuccess156acRegs. cbn.
    rewrite lookup_insert writeSuccess156acNextPcExact. reflexivity. }
  have Hx9After :
      (writeSuccess156acAfter regs global).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess156acAfter, writeSuccess15694Local. cbn.
    rewrite writeSuccess156acRegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_156ac (writeSuccess156acBefore regs global, log)
    remaining HpcBefore Hx9 Hrange).
  rewrite (rank_15694_at_156b0 (writeSuccess156acAfter regs global, log)
    remaining HpcAfter Hx9After Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsSegment156acExistsAndDecreases regs global log
    remaining oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  writeSuccessTraceAssumptions (writeSuccess156acBefore regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess156acBefore regs global)
      observations after /\
    after = writeSuccess156acAfter regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess156acBefore regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess156acObservations regs global),
    (writeSuccess156acAfter regs global).
  split.
  - exact (proj1 (segment_156ac regs global oldX1 Hpc Hx1 Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess156acAfter, writeSuccess15694Local. cbn.
      eapply writeSuccess156acRegsDom; eassumption.
    + eapply writeSuccessWithdrawals156acRankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment156acDecreases regs global log
    remaining oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  writeSuccessTraceAssumptions (writeSuccess156acBefore regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    observations after ->
  after = writeSuccess156acAfter regs global /\
  observations = writeSuccess156acObservations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess156acBefore regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_156ac_covered regs global oldX1 observations after Hpc Hx1
    Hcode Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess156acAfter, writeSuccess15694Local. cbn.
    eapply writeSuccess156acRegsDom; eassumption.
  - eapply writeSuccessWithdrawals156acRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase156ac.
Print Assumptions writeSuccessWithdrawalsPhase156b0.
Print Assumptions rank_15694_at_156ac.
Print Assumptions rank_15694_at_156b0.
Print Assumptions writeSuccessWithdrawals156acRankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment156acExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment156acDecreases.
