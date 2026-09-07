From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e0.
Require Import IslaTraces.write_success_02.a101e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals101e0IndexRankDecreases regs global log
    remaining index (source : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess101e0After regs global source
      (Z_to_bv 64 (Z.of_nat index)), log) <
    rank_15694 (writeSuccess101e0Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hindex Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess101e0Before regs global, log) = Some 0x101e0.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101e0Before,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess101e0After regs global source
        (Z_to_bv 64 (Z.of_nat index)), log) = Some 0x101e4.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101e0After,
      writeSuccess15694Local, writeSuccess101e0Regs. cbn.
    rewrite lookup_insert writeSuccess101e0NextPcExact. reflexivity. }
  have Hx15After :
      (writeSuccess101e0After regs global source
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x15" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))).
  { unfold writeSuccess101e0After, writeSuccess15694Local. cbn.
    rewrite writeSuccess101e0RegsLookupOther; try discriminate. exact Hx15. }
  have Hx9After :
      (writeSuccess101e0After regs global source
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess101e0After, writeSuccess15694Local. cbn.
    rewrite writeSuccess101e0RegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_101e0_index
    (writeSuccess101e0Before regs global, log) remaining index
    HpcBefore Hx15 Hindex Hx9 Hrange).
  rewrite (rank_15694_at_101e4_index
    (writeSuccess101e0After regs global source
      (Z_to_bv 64 (Z.of_nat index)), log) remaining index
    HpcAfter Hx15After Hindex Hx9After Hrange).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101e0IndexExistsAndDecreases
    regs global log remaining index (source : bv 64) oldX13 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits source) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x13" = Some oldX13 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  writeSuccessTraceAssumptions (writeSuccess101e0Before regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101e0Before regs global)
      observations after /\
    after = writeSuccess101e0After regs global source
      (Z_to_bv 64 (Z.of_nat index)) /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101e0Before regs global, log).
Proof.
  intros Hpc Hsource Hx15 Hx13 Hx9 Hcode Hnext Hassumptions Hindex Hrange.
  exists (writeSuccess101e0Observations regs global source
      (Z_to_bv 64 (Z.of_nat index))),
    (writeSuccess101e0After regs global source
      (Z_to_bv 64 (Z.of_nat index))).
  split.
  - exact (proj1 (segment_101e0 regs global source
      (Z_to_bv 64 (Z.of_nat index)) oldX13 Hpc Hsource Hx15 Hx13
      Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess101e0After, writeSuccess15694Local. cbn.
      eapply writeSuccess101e0RegsDom; eassumption.
    + eapply writeSuccessWithdrawals101e0IndexRankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101e0IndexDecreases
    regs global log remaining index (source : bv 64) oldX13
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits source) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x13" = Some oldX13 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  writeSuccessTraceAssumptions (writeSuccess101e0Before regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101e0Before regs global)
    observations after ->
  after = writeSuccess101e0After regs global source
    (Z_to_bv 64 (Z.of_nat index)) /\
  observations = writeSuccess101e0Observations regs global source
    (Z_to_bv 64 (Z.of_nat index)) /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101e0Before regs global, log).
Proof.
  intros Hpc Hsource Hx15 Hx13 Hx9 Hcode Hnext Hassumptions Hindex Hrange
    Hsegment.
  destruct (segment_101e0_covered regs global source
    (Z_to_bv 64 (Z.of_nat index)) oldX13 observations after Hpc Hsource
    Hx15 Hx13 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101e0After, writeSuccess15694Local. cbn.
    eapply writeSuccess101e0RegsDom; eassumption.
  - eapply writeSuccessWithdrawals101e0IndexRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawals101e0IndexRankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment101e0IndexExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101e0IndexDecreases.
