From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_96.a156e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsIteration410NonfinalBoundary finalRegs finalGlobal
    sp pointer remaining withdrawal :
  Z_to_bv 64 (Z.of_nat (S remaining)) <> (BV 64 0) ->
  writeSuccessWithdrawalsInstructionTable
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2 ->
  let after := writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal
    sp pointer (S remaining) withdrawal in
  IslaInstructionBoundary after /\
  after.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc (after, []) = Some 0x15694.
Proof.
  intros Hnonzero Htable. cbn.
  unfold writeSuccessWithdrawalsIteration410Machine, writeSuccess156e4After.
  destruct decide as [Hzero|Hvalue]; first contradiction.
  unfold writeSuccess156e4TakenAfter, writeSuccess15694Local.
  destruct writeSuccess156e4PcValues as (_ & Htaken).
  split.
  - split; first reflexivity.
    exists (Z_to_bv 64 0x15694), a15694. cbn.
    rewrite lookup_insert Htaken.
    have Hcode := Htable 0x15694 a15694 ltac:(cbn; tauto).
    rewrite Hcode. repeat split; reflexivity.
  - split; first reflexivity.
    unfold writeSuccessWithdrawalsConcretePc. cbn.
    rewrite lookup_insert Htaken. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsIteration410LastBoundary finalRegs finalGlobal sp
    pointer withdrawal :
  writeSuccessWithdrawalsInstructionTable
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2 ->
  let after := writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal
    sp pointer 0 withdrawal in
  IslaInstructionBoundary after /\
  after.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc (after, []) = Some 0x156e8.
Proof.
  intros Htable. cbn.
  unfold writeSuccessWithdrawalsIteration410Machine, writeSuccess156e4After.
  destruct decide as [Hzero|Hvalue];
    last (exfalso; apply Hvalue; bv_solve).
  unfold writeSuccess156e4FallthroughAfter, writeSuccess15694Local.
  destruct writeSuccess156e4PcValues as (Hfallthrough & _).
  split.
  - split; first reflexivity.
    exists (Z_to_bv 64 0x156e8), a156e8. cbn.
    rewrite lookup_insert Hfallthrough.
    have Hcode := Htable 0x156e8 a156e8 ltac:(cbn; tauto).
    rewrite Hcode. repeat split; reflexivity.
  - split; first reflexivity.
    unfold writeSuccessWithdrawalsConcretePc. cbn.
    rewrite lookup_insert Hfallthrough. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsIteration410NonfinalBoundary.
Print Assumptions writeSuccessWithdrawalsIteration410LastBoundary.
