From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import IslaTraces.write_success_02.a101ec.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals101e8IndexRankDecreases regs global log
    remaining index (base : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess101e8After regs global base
      (Z_to_bv 64 (Z.of_nat index)), log) <
    rank_15694 (writeSuccess101e8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hindex Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess101e8Before regs global, log) = Some 0x101e8.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101e8Before,
      writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess101e8After regs global base
        (Z_to_bv 64 (Z.of_nat index)), log) = Some 0x101ec.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101e8After,
      writeSuccess15694Local, writeSuccess101e8Regs. cbn.
    rewrite lookup_insert writeSuccess101e8NextPcExact. reflexivity. }
  have Hx15After :
      (writeSuccess101e8After regs global base
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x15" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))).
  { unfold writeSuccess101e8After, writeSuccess15694Local. cbn.
    rewrite writeSuccess101e8RegsLookupOther; try discriminate. exact Hx15. }
  have Hx9After :
      (writeSuccess101e8After regs global base
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess101e8After, writeSuccess15694Local. cbn.
    rewrite writeSuccess101e8RegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_101e8_index
    (writeSuccess101e8Before regs global, log) remaining index
    HpcBefore Hx15 Hindex Hx9 Hrange).
  rewrite (rank_15694_at_101ec_index
    (writeSuccess101e8After regs global base
      (Z_to_bv 64 (Z.of_nat index)), log) remaining index
    HpcAfter Hx15After Hindex Hx9After Hrange).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101e8IndexExistsAndDecreases
    regs global log remaining index (base : bv 64) oldX14 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits base) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x14" = Some oldX14 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  writeSuccessTraceAssumptions (writeSuccess101e8Before regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101e8Before regs global)
      observations after /\
    after = writeSuccess101e8After regs global base
      (Z_to_bv 64 (Z.of_nat index)) /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101e8Before regs global, log).
Proof.
  intros Hpc Hbase Hx15 Hx14 Hx9 Hcode Hnext Hassumptions Hindex Hrange.
  exists (writeSuccess101e8Observations regs global base
      (Z_to_bv 64 (Z.of_nat index))),
    (writeSuccess101e8After regs global base
      (Z_to_bv 64 (Z.of_nat index))).
  split.
  - exact (proj1 (segment_101e8 regs global base
      (Z_to_bv 64 (Z.of_nat index)) oldX14 Hpc Hbase Hx15 Hx14
      Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess101e8After, writeSuccess15694Local. cbn.
      eapply writeSuccess101e8RegsDom; eassumption.
    + eapply writeSuccessWithdrawals101e8IndexRankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101e8IndexDecreases
    regs global log remaining index (base : bv 64) oldX14
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits base) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x14" = Some oldX14 ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  writeSuccessTraceAssumptions (writeSuccess101e8Before regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    observations after ->
  after = writeSuccess101e8After regs global base
    (Z_to_bv 64 (Z.of_nat index)) /\
  observations = writeSuccess101e8Observations regs global base
    (Z_to_bv 64 (Z.of_nat index)) /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101e8Before regs global, log).
Proof.
  intros Hpc Hbase Hx15 Hx14 Hx9 Hcode Hnext Hassumptions Hindex Hrange
    Hsegment.
  destruct (segment_101e8_covered regs global base
    (Z_to_bv 64 (Z.of_nat index)) oldX14 observations after Hpc Hbase Hx15
    Hx14 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101e8After, writeSuccess15694Local. cbn.
    eapply writeSuccess101e8RegsDom; eassumption.
  - eapply writeSuccessWithdrawals101e8IndexRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawals101e8IndexRankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment101e8IndexExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101e8IndexDecreases.
