Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Contracts.IslarisCode.

Lemma zesu_bv_sign_extend_64_idemp (value : bv 64) :
  bv_sign_extend 64 value = value.
Proof. apply bv_sign_extend_idemp. Qed.
Print Assumptions zesu_bv_sign_extend_64_idemp.

Lemma zesu_bv_unsigned_Z_to_bv_small (n : N) (value : Z) :
  (0 <= value < bv_modulus n)%Z ->
  bv_unsigned (Z_to_bv n value) = value.
Proof.
  intros Hbound. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. exact Hbound.
Qed.
Print Assumptions zesu_bv_unsigned_Z_to_bv_small.

Create HintDb zesu_selectors.

#[export] Hint Rewrite zesu_bv_sign_extend_64_idemp
  (@bv_sign_extend_idemp 64) zesu_bv_sign_extend_same
  : isla_coq_rewrite lithium_rewrite.
#[export] Hint Rewrite zesu_bv_unsigned_add_Z_64
  zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[export] Hint Rewrite zesu_bv_unsigned_Z_to_bv_small using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[export] Hint Rewrite Z_to_bv_add Z_to_bv_unsigned
  : lithium_rewrite.
