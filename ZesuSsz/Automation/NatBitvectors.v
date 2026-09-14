Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.

Lemma zesu_nat_successor_bv64_nonzero (remaining : nat) :
  (S remaining < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
Proof.
  intros Hbound Hz.
  have HboundZ := (proj1 (Nat2Z.inj_lt (S remaining) (2 ^ 64))) Hbound.
  rewrite Nat2Z.inj_pow in HboundZ.
  have Hrange : 0 <= Z.of_nat (S remaining) < bv_modulus 64.
  { split; [apply Nat2Z.is_nonneg |]. exact HboundZ. }
  have Hu := f_equal bv_unsigned Hz.
  rewrite Z_to_bv_small in Hu; [|exact Hrange].
  change (Z.of_nat (S remaining) = Z.of_nat O) in Hu.
  apply Nat2Z.inj in Hu. discriminate.
Qed.
Print Assumptions zesu_nat_successor_bv64_nonzero.
