From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsTailBoundaryZero regs global pointer :
  writeSuccessWithdrawalsInstructionTable global ->
  let after := writeSuccess156e4After (BV 64 0)
    (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
      (Z_to_bv 64 1)) global in
  IslaInstructionBoundary after /\
  after.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc (after, []) = Some 0x156e8.
Proof.
  intros Htable. cbn zeta.
  unfold writeSuccess156e4After.
  destruct decide as [Heq|Hneq]; last contradiction.
  unfold writeSuccess156e4FallthroughAfter, IslaInstructionBoundary.
  split.
  - split; first reflexivity. exists (Z_to_bv 64 0x156e8), IslaTraces.write_success_96.a156e8.a156e8.
    split.
    + unfold writeSuccess156e4FallthroughRegs. rewrite lookup_insert.
      destruct writeSuccess156e4PcValues as (-> & _). reflexivity.
    + split; last reflexivity. apply Htable. cbn. tauto.
  - split; first reflexivity.
    unfold writeSuccessWithdrawalsConcretePc. cbn.
    unfold writeSuccess156e4FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess156e4PcValues as (-> & _). reflexivity.
Qed.

Lemma writeSuccessWithdrawalsTailBoundaryNonzero regs global pointer value next :
  value <> (BV 64 0) ->
  writeSuccessWithdrawalsInstructionTable global ->
  let after := writeSuccess156e4After value
    (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer) next) global in
  IslaInstructionBoundary after /\
  after.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc (after, []) = Some 0x15694.
Proof.
  intros Hne Htable. cbn zeta.
  unfold writeSuccess156e4After.
  destruct decide as [Heq|Hneq]; first contradiction.
  unfold writeSuccess156e4TakenAfter, IslaInstructionBoundary.
  split.
  - split; first reflexivity. exists (Z_to_bv 64 0x15694), IslaTraces.write_success_90.a15694.a15694.
    split.
    + unfold writeSuccess156e4TakenRegs. rewrite lookup_insert.
      destruct writeSuccess156e4PcValues as (_ & ->). reflexivity.
    + split; last reflexivity. apply Htable. cbn. tauto.
  - split; first reflexivity.
    unfold writeSuccessWithdrawalsConcretePc. cbn.
    unfold writeSuccess156e4TakenRegs. rewrite lookup_insert.
    destruct writeSuccess156e4PcValues as (_ & ->). reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsTailBoundaryZero.
Print Assumptions writeSuccessWithdrawalsTailBoundaryNonzero.
