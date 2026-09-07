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
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep101d4.

Open Scope Z_scope.

Lemma writeSuccess101d8ZeroDiffersFrom48 :
  (BV 64 0 : bv 64) <> BV 64 48.
Proof. bv_solve. Qed.

Lemma writeSuccess101d8ZeroAfter regs global :
  writeSuccess101d8After (BV 64 0) (BV 64 48) regs global =
  writeSuccess101d8TakenAfter regs global.
Proof.
  unfold writeSuccess101d8After.
  destruct decide; [contradiction writeSuccess101d8ZeroDiffersFrom48 | reflexivity].
Qed.

Lemma writeSuccessWithdrawalsSegment101d8ExistsAndDecreases regs global log
    remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 0)) ->
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
  exists (writeSuccess101d8Observations (BV 64 0) (BV 64 48) regs global),
    (writeSuccess101d8After (BV 64 0) (BV 64 48) regs global).
  split.
  - eapply segment_101d8; eassumption.
  - rewrite writeSuccess101d8ZeroAfter. split; first reflexivity. split.
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
            Some (RVal_Bits (BV 64 0)).
      { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx15 | discriminate]. }
      have Hx9After :
          (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x9" =
            Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
      { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
          writeSuccess101d8TakenRegs. cbn.
        rewrite lookup_insert_ne; [exact Hx9 | discriminate]. }
      rewrite (rank_15694_at_101d8_zero
        (writeSuccess101d8Before regs global, log) remaining
        HpcBefore Hx15 Hx9 Hrange).
      rewrite (rank_15694_at_101e0_zero
        (writeSuccess101d8TakenAfter regs global, log) remaining
        HpcAfter Hx15After Hx9After Hrange).
      lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101d8Decreases regs global log
    remaining observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits (BV 64 0)) ->
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
    writeSuccess101d8Observations (BV 64 0) (BV 64 48) regs global /\
  dom after.1.(seq_regs) = dom regs /\
  rank_15694 (after, log) <
    rank_15694 (writeSuccess101d8Before regs global, log).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hx9 Hrange Hsegment.
  destruct (segment_101d8_covered regs global (BV 64 0) (BV 64 48)
    observations after Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hsegment)
    as [Hafter Hobservations].
  rewrite writeSuccess101d8ZeroAfter in Hafter. subst after.
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
          Some (RVal_Bits (BV 64 0)).
    { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx15 | discriminate]. }
    have Hx9After :
        (writeSuccess101d8TakenAfter regs global).1.(seq_regs) !! "x9" =
          Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold writeSuccess101d8TakenAfter, writeSuccess15694Local,
        writeSuccess101d8TakenRegs. cbn.
      rewrite lookup_insert_ne; [exact Hx9 | discriminate]. }
    rewrite (rank_15694_at_101d8_zero
      (writeSuccess101d8Before regs global, log) remaining
      HpcBefore Hx15 Hx9 Hrange).
    rewrite (rank_15694_at_101e0_zero
      (writeSuccess101d8TakenAfter regs global, log) remaining
      HpcAfter Hx15After Hx9After Hrange).
    lia.
Qed.

Print Assumptions writeSuccess101d8ZeroDiffersFrom48.
Print Assumptions writeSuccess101d8ZeroAfter.
Print Assumptions writeSuccessWithdrawalsSegment101d8ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101d8Decreases.
