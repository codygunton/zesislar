From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b4.
Require Import IslaTraces.write_success_93.a156c0.
Require Import IslaTraces.write_success_95.a156dc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Definition writeSuccessEncoderIntReturnFacts
    (global : seq_global_state) (returnAddress : bv 64) : Prop :=
  bv_extract 0 2 returnAddress = BV 2 0 /\
  exists returnTrace,
    global.(seq_instrs) !! returnAddress = Some returnTrace.

Lemma writeSuccessEncoderIntCaller156b4 global :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessEncoderIntReturnFacts global (Z_to_bv 64 0x156b4).
Proof.
  intros Htable. split.
  - apply bv_eq. native_compute. reflexivity.
  - exists IslaTraces.write_success_92.a156b4.a156b4.
    apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Lemma writeSuccessEncoderIntCaller156c0 global :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessEncoderIntReturnFacts global (Z_to_bv 64 0x156c0).
Proof.
  intros Htable. split.
  - apply bv_eq. native_compute. reflexivity.
  - exists IslaTraces.write_success_93.a156c0.a156c0.
    apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Lemma writeSuccessEncoderIntCaller156dc global :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessEncoderIntReturnFacts global (Z_to_bv 64 0x156dc).
Proof.
  intros Htable. split.
  - apply bv_eq. native_compute. reflexivity.
  - exists IslaTraces.write_success_95.a156dc.a156dc.
    apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Print Assumptions writeSuccessEncoderIntCaller156b4.
Print Assumptions writeSuccessEncoderIntCaller156c0.
Print Assumptions writeSuccessEncoderIntCaller156dc.
