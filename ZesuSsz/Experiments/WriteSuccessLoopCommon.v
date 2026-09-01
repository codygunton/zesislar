From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma bv_unsigned_add_no_wrap_64 (left right : bv 64) :
  (bv_unsigned left + bv_unsigned right < 2 ^ 64)%Z ->
  bv_unsigned (left + right)%bv = bv_unsigned left + bv_unsigned right.
Proof.
  move => Hsum. rewrite bv_add_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 left).
  pose proof (bv_unsigned_in_range 64 right).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Definition writeSuccessFixedWidthArrayInvariant `{!islaG Sigma}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) : iProp Sigma :=
  (⌜total = (processed + S remaining)%nat⌝ ∗
   ⌜length bytes = (32 * total)%nat⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessFixedWidthArrayInvariant) := I.
