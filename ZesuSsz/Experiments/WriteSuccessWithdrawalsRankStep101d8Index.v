From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101dc.
Require Import IslaTraces.write_success_02.a101e0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Open Scope Z_scope.

Lemma writeSuccess101d8IndexDiffersFrom48 index :
  (index < 48)%nat ->
  (Z_to_bv 64 (Z.of_nat index) : bv 64) <> BV 64 48.
Proof.
  intros Hindex Heq. apply (f_equal bv_unsigned) in Heq.
  have Hsmall : (0 <= Z.of_nat index < bv_modulus 64)%Z.
  { unfold bv_modulus. cbn. lia. }
  rewrite Z_to_bv_small in Heq; last exact Hsmall.
  rewrite bv_unsigned_BV in Heq. lia.
Qed.

Lemma writeSuccess101d8IndexAfter regs global index :
  (index < 48)%nat ->
  writeSuccess101d8After (Z_to_bv 64 (Z.of_nat index)) (BV 64 48)
    regs global = writeSuccess101d8TakenAfter regs global.
Proof.
  intros Hindex. unfold writeSuccess101d8After.
  destruct decide as [Heq|Hne].
  - exfalso. exact (writeSuccess101d8IndexDiffersFrom48 index Hindex Heq).
  - reflexivity.
Qed.

Lemma writeSuccessWithdrawals101d8IndexRankDecreases before after
    remaining index :
  writeSuccessWithdrawalsConcretePc before = Some 0x101d8 ->
  before.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  writeSuccessWithdrawalsConcretePc after = Some 0x101e0 ->
  after.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 after < rank_15694 before.
Proof.
  intros HpcBefore Hx15Before Hx9Before HpcAfter Hx15After Hx9After
    Hindex Hrange.
  rewrite (rank_15694_at_101d8_index before remaining index HpcBefore
    Hx15Before ltac:(lia) Hx9Before Hrange).
  rewrite (rank_15694_at_101e0_index after remaining index HpcAfter
    Hx15After Hindex Hx9After Hrange).
  lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101d8IndexExistsAndDecreases
    regs global log remaining index :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x12" = Some (RVal_Bits (BV 64 48)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101d8Before regs global)
      observations after /\
    after = writeSuccess101d8TakenAfter regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101d8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hx9 Hindex Hrange.
  exists (writeSuccess101d8Observations
      (Z_to_bv 64 (Z.of_nat index)) (BV 64 48) regs global),
    (writeSuccess101d8After
      (Z_to_bv 64 (Z.of_nat index)) (BV 64 48) regs global).
  split.
  - eapply segment_101d8; eassumption.
  - rewrite writeSuccess101d8IndexAfter; last exact Hindex.
    split; first reflexivity. split.
    + unfold writeSuccess101d8TakenAfter, writeSuccess15694Local. cbn.
      apply elem_of_dom_2 in Hpc.
      unfold writeSuccess101d8TakenRegs. rewrite dom_insert_L. set_solver.
    + eapply writeSuccessWithdrawals101d8IndexRankDecreases.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8Before,
          writeSuccess15694Local. cbn. rewrite Hpc. reflexivity.
      * exact Hx15.
      * exact Hx9.
      * unfold writeSuccessWithdrawalsConcretePc,
          writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert. vm_compute. reflexivity.
      * unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx15 | discriminate].
      * unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx9 | discriminate].
      * exact Hindex.
      * exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101d8IndexDecreases
    regs global log remaining index observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  regs !! "x12" = Some (RVal_Bits (BV 64 48)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (index < 48)%nat ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    observations after ->
  after = writeSuccess101d8TakenAfter regs global /\
  observations = writeSuccess101d8Observations
    (Z_to_bv 64 (Z.of_nat index)) (BV 64 48) regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101d8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hx9 Hindex Hrange
    Hsegment.
  destruct (segment_101d8_covered regs global
    (Z_to_bv 64 (Z.of_nat index)) (BV 64 48) observations after Hpc Hx15
    Hx12 Hcode Hfall Htaken Hassumptions Hsegment) as [Hafter Hobservations].
  rewrite writeSuccess101d8IndexAfter in Hafter; last exact Hindex.
  subst after. split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101d8TakenAfter, writeSuccess15694Local. cbn.
    apply elem_of_dom_2 in Hpc.
    unfold writeSuccess101d8TakenRegs. rewrite dom_insert_L. set_solver.
  - eapply writeSuccessWithdrawals101d8IndexRankDecreases.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8Before,
        writeSuccess15694Local. cbn. rewrite Hpc. reflexivity.
    + exact Hx15.
    + exact Hx9.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert. vm_compute. reflexivity.
    + unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx15 | discriminate].
    + unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx9 | discriminate].
    + exact Hindex.
    + exact Hrange.
Qed.

Print Assumptions writeSuccess101d8IndexDiffersFrom48.
Print Assumptions writeSuccess101d8IndexAfter.
Print Assumptions writeSuccessWithdrawals101d8IndexRankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment101d8IndexExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101d8IndexDecreases.
