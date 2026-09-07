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
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep101f4.

Open Scope Z_scope.

Lemma writeSuccess101d8OneDiffersFrom48 :
  (BV 64 1 : bv 64) <> BV 64 48.
Proof. bv_solve. Qed.

Lemma writeSuccess101d8OneAfter regs global :
  writeSuccess101d8After (BV 64 1) (BV 64 48) regs global =
  writeSuccess101d8TakenAfter regs global.
Proof.
  unfold writeSuccess101d8After.
  destruct decide; [contradiction writeSuccess101d8OneDiffersFrom48 | reflexivity].
Qed.

Lemma writeSuccessWithdrawalsPhase101e0One state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 396%nat.
Proof.
  intros Hpc Hx15. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_101e0_one state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 396)%nat.
Proof.
  intros Hpc Hx15 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101e0One state Hpc Hx15.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 396 =
    410 * remaining + 396)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsSegment101d8OneExistsAndDecreases regs global log
    remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  regs !! "x12" = Some (RVal_Bits (BV 64 48)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  exists observations after,
    IslaInstructionSegment (writeSuccess101d8Before regs global)
      observations after /\
    after = writeSuccess101d8TakenAfter regs global /\
    dom after.1.(seq_regs) = dom regs /\
    rank_15694 (after, log) <
      rank_15694 (writeSuccess101d8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hx9 Hrange.
  exists (writeSuccess101d8Observations (BV 64 1) (BV 64 48) regs global),
    (writeSuccess101d8After (BV 64 1) (BV 64 48) regs global).
  split.
  - eapply segment_101d8; eassumption.
  - rewrite writeSuccess101d8OneAfter. split; first reflexivity. split.
    + unfold writeSuccess101d8TakenAfter, writeSuccess15694Local. cbn.
      apply elem_of_dom_2 in Hpc.
      unfold writeSuccess101d8TakenRegs. rewrite dom_insert_L. set_solver.
    + have HpcBefore :
          writeSuccessWithdrawalsConcretePc
            (writeSuccess101d8Before regs global, log) = Some 0x101d8.
      { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8Before,
          writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
      have HpcAfter :
          writeSuccessWithdrawalsConcretePc
            (writeSuccess101d8TakenAfter regs global, log) = Some 0x101e0.
      { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8TakenAfter,
          writeSuccess15694Local, writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert. vm_compute. reflexivity. }
      have Hx15After :
          (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x15" =
            Some (RVal_Bits (BV 64 1)).
      { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx15 | discriminate]. }
      have Hx9After :
          (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x9" =
            Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
      { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx9 | discriminate]. }
      rewrite (rank_15694_at_101d8_one
        (writeSuccess101d8Before regs global, log) remaining
        HpcBefore Hx15 Hx9 Hrange).
      rewrite (rank_15694_at_101e0_one
        (writeSuccess101d8TakenAfter regs global, log) remaining
        HpcAfter Hx15After Hx9After Hrange).
      lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101d8OneDecreases regs global log
    remaining observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 1)) ->
  regs !! "x12" = Some (RVal_Bits (BV 64 48)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    observations after ->
  after = writeSuccess101d8TakenAfter regs global /\
  observations =
    writeSuccess101d8Observations (BV 64 1) (BV 64 48) regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101d8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hx9 Hrange Hsegment.
  destruct (segment_101d8_covered regs global (BV 64 1) (BV 64 48)
    observations after Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hsegment)
    as [Hafter Hobservations].
  rewrite writeSuccess101d8OneAfter in Hafter. subst after.
  split; first reflexivity. split; first exact Hobservations. split.
  - unfold writeSuccess101d8TakenAfter, writeSuccess15694Local. cbn.
    apply elem_of_dom_2 in Hpc.
    unfold writeSuccess101d8TakenRegs. rewrite dom_insert_L. set_solver.
  - have HpcBefore :
        writeSuccessWithdrawalsConcretePc
          (writeSuccess101d8Before regs global, log) = Some 0x101d8.
    { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8Before,
        writeSuccess15694Local. cbn. rewrite Hpc. reflexivity. }
    have HpcAfter :
        writeSuccessWithdrawalsConcretePc
          (writeSuccess101d8TakenAfter regs global, log) = Some 0x101e0.
    { unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8TakenAfter,
        writeSuccess15694Local, writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert. vm_compute. reflexivity. }
    have Hx15After :
        (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x15" =
          Some (RVal_Bits (BV 64 1)).
    { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx15 | discriminate]. }
    have Hx9After :
        (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x9" =
          Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx9 | discriminate]. }
    rewrite (rank_15694_at_101d8_one
      (writeSuccess101d8Before regs global, log) remaining
      HpcBefore Hx15 Hx9 Hrange).
    rewrite (rank_15694_at_101e0_one
      (writeSuccess101d8TakenAfter regs global, log) remaining
      HpcAfter Hx15After Hx9After Hrange).
    lia.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase101e0One.
Print Assumptions rank_15694_at_101e0_one.
Print Assumptions writeSuccess101d8OneDiffersFrom48.
Print Assumptions writeSuccess101d8OneAfter.
Print Assumptions writeSuccessWithdrawalsSegment101d8OneExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101d8OneDecreases.
