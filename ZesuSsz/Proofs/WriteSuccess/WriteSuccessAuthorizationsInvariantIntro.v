Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Import ListNotations.

Lemma write_success_pure_sep_3 `{!islaG Sigma}
    (p1 p2 p3 : Prop) (R : iProp Sigma) :
  p1 -> p2 -> p3 -> R -∗ ⌜p1⌝ ∗ ⌜p2⌝ ∗ ⌜p3⌝ ∗ R.
Proof. move => *. zesu_block. Qed.

Lemma write_success_pure_sep_12 `{!islaG Sigma}
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) :
  p1 -> p2 -> p3 -> p4 -> p5 -> p6 -> p7 -> p8 -> p9 -> p10 -> p11 ->
  p12 ->
  ⊢@{iPropI Sigma} ⌜p1⌝ ∗ ⌜p2⌝ ∗ ⌜p3⌝ ∗ ⌜p4⌝ ∗ ⌜p5⌝ ∗ ⌜p6⌝ ∗
    ⌜p7⌝ ∗ ⌜p8⌝ ∗ ⌜p9⌝ ∗ ⌜p10⌝ ∗ ⌜p11⌝ ∗ ⌜p12⌝ ∗ True.
Proof. move => *. zesu_block. Qed.

Lemma write_success_authorizations_invariant_zero_intro
    `{!islaG Sigma} (sp pointer : bv 64) (remaining : nat)
    (bytes : list (bv 8))
    (Hbytes : length bytes = (144 * S remaining)%nat)
    (Hbound : (S remaining < 2 ^ 64)%nat)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (HspMin : ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z)
    (HspMax : (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z)
    (HbaseMin : ((mapRamBase defaultMap) <= bv_unsigned pointer)%Z)
    (HbaseMax :
      (bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z) :
  ⊢ writeSuccessAuthorizationsInvariant sp pointer (bv_unsigned pointer)
    (S remaining) 0%nat remaining bytes [] bytes.
Proof.
  have Htotal : S remaining = (0 + S remaining)%nat by reflexivity.
  have Hsplit : bytes = [] ++ bytes by reflexivity.
  have Hprefix : length (@nil (bv 8)) = (144 * 0)%nat by reflexivity.
  have Hpointer : bv_unsigned pointer =
      (bv_unsigned pointer + 144 * Z.of_nat 0)%Z.
  { rewrite Nat2Z.inj_0 Z.mul_0_r Z.add_0_r. reflexivity. }
  unfold writeSuccessAuthorizationsInvariant.
  apply write_success_pure_sep_12; assumption.
Qed.
