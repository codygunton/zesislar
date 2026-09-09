From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Definition writeSuccessOutputReturnFacts
    (global : seq_global_state) (returnAddress : bv 64) : Prop :=
  bv_extract 0 2 returnAddress = BV 2 0 /\
  exists returnTrace,
    global.(seq_instrs) !! returnAddress = Some returnTrace.

Lemma writeSuccessOutputCaller156d0 global :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessOutputReturnFacts global (Z_to_bv 64 0x156d0).
Proof.
  intros Htable. split.
  - apply bv_eq. native_compute. reflexivity.
  - exists IslaTraces.write_success_94.a156d0.a156d0.
    apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Print Assumptions writeSuccessOutputCaller156d0.

