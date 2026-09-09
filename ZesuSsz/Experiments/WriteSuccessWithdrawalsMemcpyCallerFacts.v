From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Definition writeSuccessMemcpyReturnFacts
    (global : seq_global_state) (returnAddress : bv 64) : Prop :=
  bv_extract 0 2 returnAddress = BV 2 0 /\
  exists returnTrace,
    global.(seq_instrs) !! returnAddress = Some returnTrace.

Lemma writeSuccessMemcpyCaller156a8 global :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessMemcpyReturnFacts global (Z_to_bv 64 0x156a8).
Proof.
  intros Htable. split.
  - apply bv_eq. native_compute. reflexivity.
  - exists IslaTraces.write_success_91.a156a8.a156a8.
    apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Print Assumptions writeSuccessMemcpyCaller156a8.
