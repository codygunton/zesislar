From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101ec.
Require Import IslaTraces.write_success_02.a101f0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ec.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ecCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Open Scope Z_scope.

Lemma writeSuccess101ecIndexNext index :
  (Z_to_bv 64 (Z.of_nat index) + BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (S index)).
Proof.
  change ((Z_to_bv 64 (Z.of_nat index) + Z_to_bv 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (S index))).
  rewrite Z_to_bv_add. f_equal. lia.
Qed.

Lemma writeSuccessWithdrawals101ecIndexRankDecreases regs global log
    remaining index :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 (writeSuccess101ecAfter regs global
      (Z_to_bv 64 (Z.of_nat index)), log) <
    rank_15694 (writeSuccess101ecBefore regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hindex Hrange.
  have HpcBefore : writeSuccessWithdrawalsConcretePc
      (writeSuccess101ecBefore regs global, log) = Some 0x101ec.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101ecBefore,
      writeSuccess101ecLocal. cbn. rewrite Hpc. reflexivity. }
  have HpcAfter : writeSuccessWithdrawalsConcretePc
      (writeSuccess101ecAfter regs global
        (Z_to_bv 64 (Z.of_nat index)), log) = Some 0x101f0.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101ecAfter,
      writeSuccess101ecLocal, writeSuccess101ecRegs. cbn.
    rewrite lookup_insert writeSuccess101ecNextPcExact. reflexivity. }
  have Hx15After :
      (writeSuccess101ecAfter regs global
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x15" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S index)))).
  { unfold writeSuccess101ecAfter, writeSuccess101ecLocal,
      writeSuccess101ecRegs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert writeSuccess101ecIndexNext. reflexivity. }
  have Hx9After :
      (writeSuccess101ecAfter regs global
        (Z_to_bv 64 (Z.of_nat index))).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess101ecAfter, writeSuccess101ecLocal. cbn.
    rewrite writeSuccess101ecRegsLookupOther; try discriminate. exact Hx9. }
  rewrite (rank_15694_at_101ec_index
    (writeSuccess101ecBefore regs global, log) remaining index
    HpcBefore Hx15 Hindex Hx9 Hrange).
  rewrite (rank_15694_at_101f0_index
    (writeSuccess101ecAfter regs global
      (Z_to_bv 64 (Z.of_nat index)), log) remaining (S index)
    HpcAfter Hx15After ltac:(lia) Hx9After Hrange).
  lia.
Qed.

Lemma writeSuccess101ecIndexRegsDom regs index :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  dom (writeSuccess101ecRegs regs (Z_to_bv 64 (Z.of_nat index))) = dom regs.
Proof.
  intros Hpc Hx15. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx15.
  unfold writeSuccess101ecRegs. rewrite !dom_insert_L. set_solver.
Qed.

Lemma writeSuccessWithdrawalsSegment101ecIndexExistsAndDecreases
    regs global log remaining index :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  writeSuccessTraceAssumptions (writeSuccess101ecBefore regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101ecBefore regs global)
      observations after /\
    after = writeSuccess101ecAfter regs global
      (Z_to_bv 64 (Z.of_nat index)) /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101ecBefore regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hindex Hrange.
  exists (writeSuccess101ecObservations regs global
      (Z_to_bv 64 (Z.of_nat index))),
    (writeSuccess101ecAfter regs global (Z_to_bv 64 (Z.of_nat index))).
  split.
  - exact (proj1 (segment_101ec regs global
      (Z_to_bv 64 (Z.of_nat index))
      (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) Hpc Hx15 Hx15
      Hcode Hnext Hassumptions)).
  - split; first reflexivity. split.
    + unfold writeSuccess101ecAfter, writeSuccess101ecLocal. cbn.
      apply writeSuccess101ecIndexRegsDom; assumption.
    + eapply writeSuccessWithdrawals101ecIndexRankDecreases; eassumption.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101ecIndexDecreases
    regs global log remaining index observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  writeSuccessTraceAssumptions (writeSuccess101ecBefore regs global) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101ecBefore regs global)
    observations after ->
  after = writeSuccess101ecAfter regs global
    (Z_to_bv 64 (Z.of_nat index)) /\
  observations = writeSuccess101ecObservations regs global
    (Z_to_bv 64 (Z.of_nat index)) /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101ecBefore regs global, log).
Proof.
  intros Hpc Hx15 Hx9 Hcode Hnext Hassumptions Hindex Hrange Hsegment.
  destruct (segment_101ec_covered regs global
    (Z_to_bv 64 (Z.of_nat index))
    (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) observations after Hpc Hx15
    Hx15 Hcode Hnext Hassumptions Hsegment) as [Hafter Hobservations].
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101ecAfter, writeSuccess101ecLocal. cbn.
    apply writeSuccess101ecIndexRegsDom; assumption.
  - eapply writeSuccessWithdrawals101ecIndexRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccess101ecIndexNext.
Print Assumptions writeSuccessWithdrawals101ecIndexRankDecreases.
Print Assumptions writeSuccess101ecIndexRegsDom.
Print Assumptions writeSuccessWithdrawalsSegment101ecIndexExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101ecIndexDecreases.
