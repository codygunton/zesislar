Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Rewrites.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma rewrites_sign_extend_boundary (value : bv 64) :
  bv_sign_extend 64 (bv_sign_extend 64 value) = value.
Proof. autorewrite with isla_coq_rewrite. reflexivity. Qed.
Print Assumptions rewrites_sign_extend_boundary.

Lemma rewrites_unsigned_no_local_hint (value : Z) :
  (0 <= value < bv_modulus 64)%Z ->
  bv_unsigned (Z_to_bv 64 value) = value.
Proof. intros Hbound. autorewrite with isla_coq_rewrite. reflexivity. Qed.
Print Assumptions rewrites_unsigned_no_local_hint.

Definition rewrites_row_word (bytes : list (bv 8))
    (index offset : nat) : bv 64 :=
  Z_to_bv 64
    (little_endian_to_bv 8 (take 8 (drop (index + offset)%nat bytes))).
#[export] Hint Unfold rewrites_row_word : zesu_selectors.

Lemma rewrites_selector_word (bytes : list (bv 8))
    (index offset : nat) :
  rewrites_row_word bytes index offset =
    Z_to_bv 64
      (little_endian_to_bv 8 (take 8 (drop (index + offset)%nat bytes))).
Proof. zesu_finish_selectors. Qed.
Print Assumptions rewrites_selector_word.

Lemma rewrites_selector_stack_index (sp : bv 64) :
  ((mapRamBase defaultMap) <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 16 < machineRamEnd defaultMap)%Z ->
  Z.to_nat (bv_unsigned (sp + BV 64 8)%bv -
    (bv_unsigned sp + 0)) = 8%nat.
Proof. intros Hlower Hupper. zesu_finish_selectors. Qed.
Print Assumptions rewrites_selector_stack_index.
