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
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals101f4IndexRankDecreases before after
    remaining index :
  writeSuccessWithdrawalsConcretePc before = Some 0x101f4 ->
  before.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  writeSuccessWithdrawalsConcretePc after = Some 0x101d8 ->
  after.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (0 < index <= 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 after < rank_15694 before.
Proof.
  intros HpcBefore Hx15Before Hx9Before HpcAfter Hx15After Hx9After
    Hindex Hrange.
  rewrite (rank_15694_at_101f4_index before remaining index HpcBefore
    Hx15Before Hindex Hx9Before Hrange).
  rewrite (rank_15694_at_101d8_index after remaining index HpcAfter
    Hx15After ltac:(lia) Hx9After Hrange).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101f4IndexExistsAndDecreases
    regs global log remaining index :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  regs !! "x15" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  writeSuccessTraceAssumptions (writeSuccess101f4Before regs global) ->
  (0 < index <= 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101f4Before regs global)
      observations after /\
    after = writeSuccess101f4After regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101f4Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hindex Hrange.
  exists (writeSuccess101f4Observations regs global),
    (writeSuccess101f4After regs global).
  split.
  - exact (proj1 (segment_101f4 regs global Hpc Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      apply writeSuccess101f4RegsDom. exact Hpc.
    + eapply writeSuccessWithdrawals101f4IndexRankDecreases.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4Before,
          writeSuccess15694Local. cbn. rewrite Hpc. reflexivity.
      * exact Hx15.
      * exact Hx9.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4After,
          writeSuccess15694Local, writeSuccess101f4Regs. cbn.
        rewrite lookup_insert writeSuccess101f4TargetExact. reflexivity.
      * unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
        rewrite writeSuccess101f4RegsLookupOther;
          [exact Hx15 | discriminate].
      * unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
        rewrite writeSuccess101f4RegsLookupOther;
          [exact Hx9 | discriminate].
      * exact Hindex.
      * exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101f4IndexDecreases
    regs global log remaining index observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  regs !! "x15" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  writeSuccessTraceAssumptions (writeSuccess101f4Before regs global) ->
  (0 < index <= 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    observations after ->
  after = writeSuccess101f4After regs global /\
  observations = writeSuccess101f4Observations regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101f4Before regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hindex Hrange Hsegment.
  destruct (segment_101f4_covered regs global observations after Hpc Hcode
    Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
    apply writeSuccess101f4RegsDom. exact Hpc.
  - eapply writeSuccessWithdrawals101f4IndexRankDecreases.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4Before,
        writeSuccess15694Local. cbn. rewrite Hpc. reflexivity.
    + exact Hx15.
    + exact Hx9.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess101f4After,
        writeSuccess15694Local, writeSuccess101f4Regs. cbn.
      rewrite lookup_insert writeSuccess101f4TargetExact. reflexivity.
    + unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess101f4RegsLookupOther; [exact Hx15 | discriminate].
    + unfold writeSuccess101f4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess101f4RegsLookupOther; [exact Hx9 | discriminate].
    + exact Hindex.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawals101f4IndexRankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment101f4IndexExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101f4IndexDecreases.
