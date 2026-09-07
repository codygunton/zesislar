From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPhase101f4One state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101f4 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 398%nat.
Proof.
  intros Hpc Hx15. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPhase101d8One state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 397%nat.
Proof.
  intros Hpc Hx15. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_101f4_one state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101f4 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 398)%nat.
Proof.
  intros Hpc Hx15 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101f4One state Hpc Hx15.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 398 =
    410 * remaining + 398)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_101d8_one state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 397)%nat.
Proof.
  intros Hpc Hx15 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101d8One state Hpc Hx15.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 397 =
    410 * remaining + 397)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101f4ExistsAndDecreases regs global log
    remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  writeSuccessTraceAssumptions (writeSuccess101f4Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101f4Before regs global)
      observations after /\
    after = writeSuccess101f4After regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101f4Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hrange.
  exists (writeSuccess101f4Observations regs global),
    (writeSuccess101f4After regs global).
  split.
  - exact (proj1 (segment_101f4 regs global Hpc Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      apply writeSuccess101f4RegsDom. exact Hpc.
    + have HpcBefore : writeSuccessWithdrawalsConcretePc
          (writeSuccess101f4Before regs global, log) = Some 0x101f4.
      { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4Before,
          writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
      have HpcAfter : writeSuccessWithdrawalsConcretePc
          (writeSuccess101f4After regs global, log) = Some 0x101d8.
      { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4After,
          writeSuccess15694Local, writeSuccess101f4Regs. cbn.
        rewrite lookup_insert writeSuccess101f4TargetExact. reflexivity. }
      have Hx15After :
          (writeSuccess101f4After regs global).1.(seq_regs) !! "x15" =
            Some (RVal_Bits (BV 64 1)).
      { unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
        rewrite writeSuccess101f4RegsLookupOther; [exact Hx15 | discriminate]. }
      have Hx9After :
          (writeSuccess101f4After regs global).1.(seq_regs) !! "x9" =
            Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
      { unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
        rewrite writeSuccess101f4RegsLookupOther; [exact Hx9 | discriminate]. }
      rewrite (rank_15694_at_101f4_one
        (writeSuccess101f4Before regs global, log) remaining
        HpcBefore Hx15 Hx9 Hrange).
      rewrite (rank_15694_at_101d8_one
        (writeSuccess101f4After regs global, log) remaining
        HpcAfter Hx15After Hx9After Hrange).
      lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101f4Decreases regs global log
    remaining observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  writeSuccessTraceAssumptions (writeSuccess101f4Before regs global) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    observations after ->
  after = writeSuccess101f4After regs global /\
  observations = writeSuccess101f4Observations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101f4Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hrange Hsegment.
  destruct (segment_101f4_covered regs global observations after Hpc Hcode
    Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
    apply writeSuccess101f4RegsDom. exact Hpc.
  - have HpcBefore : writeSuccessWithdrawalsConcretePc
        (writeSuccess101f4Before regs global, log) = Some 0x101f4.
    { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4Before,
        writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
    have HpcAfter : writeSuccessWithdrawalsConcretePc
        (writeSuccess101f4After regs global, log) = Some 0x101d8.
    { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4After,
        writeSuccess15694Local, writeSuccess101f4Regs. cbn.
      rewrite lookup_insert writeSuccess101f4TargetExact. reflexivity. }
    have Hx15After :
        (writeSuccess101f4After regs global).1.(seq_regs) !! "x15" =
          Some (RVal_Bits (BV 64 1)).
    { unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess101f4RegsLookupOther; [exact Hx15 | discriminate]. }
    have Hx9After :
        (writeSuccess101f4After regs global).1.(seq_regs) !! "x9" =
          Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess101f4RegsLookupOther; [exact Hx9 | discriminate]. }
    rewrite (rank_15694_at_101f4_one
      (writeSuccess101f4Before regs global, log) remaining
      HpcBefore Hx15 Hx9 Hrange).
    rewrite (rank_15694_at_101d8_one
      (writeSuccess101f4After regs global, log) remaining
      HpcAfter Hx15After Hx9After Hrange).
    lia.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase101f4One.
Print Assumptions writeSuccessWithdrawalsPhase101d8One.
Print Assumptions rank_15694_at_101f4_one.
Print Assumptions rank_15694_at_101d8_one.
Print Assumptions writeSuccessWithdrawalsSegment101f4ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101f4Decreases.
