From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessBlockerInstructionTable :
  writeSuccessWithdrawalsInstructionTable writeSuccessBlockerGlobal.
Proof.
  intros pc trace Hsource.
  unfold writeSuccessWithdrawalsInstructionSource,
    writeSuccessWithdrawalsInstructionMap in Hsource.
  cbn in Hsource.
  unfold writeSuccessBlockerGlobal, writeSuccessBlockerInstrs. cbn.
  repeat (destruct Hsource as [Hsource | Hsource];
    [inversion Hsource; subst; native_compute; reflexivity|]).
  contradiction.
Qed.

Lemma writeSuccessBlockerBoundary :
  IslaInstructionBoundary
    (writeSuccessBlockerLocal, writeSuccessBlockerGlobal).
Proof.
  split; first reflexivity.
  exists (BV 64 0x15694), IslaTraces.write_success_90.a15694.a15694.
  split; [native_compute; reflexivity|].
  split; last reflexivity.
  change (writeSuccessBlockerGlobal.(seq_instrs) !! Z_to_bv 64 0x15694 =
    Some IslaTraces.write_success_90.a15694.a15694).
  pose proof writeSuccessBlockerInstructionTable as Htable.
  unfold writeSuccessWithdrawalsInstructionTable in Htable.
  apply Htable.
  unfold writeSuccessWithdrawalsInstructionSource,
    writeSuccessWithdrawalsInstructionMap.
  cbn. tauto.
Qed.

Print Assumptions writeSuccessBlockerInstructionTable.
Print Assumptions writeSuccessBlockerBoundary.
