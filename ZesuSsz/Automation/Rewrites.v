Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Contracts.IslarisCode.

Create HintDb zesu_contract_constants.

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

(* This offset is integer arithmetic, without a bitvector conversion. *)
Lemma zesu_integer_array_byte_equality (base offset : Z)
    (bytes : list (bv 8)) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + offset - base)) bytes))) =
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat offset) bytes))).
Proof.
  replace (Z.to_nat (base + offset - base)) with (Z.to_nat offset)
    by (f_equal; lia).
  reflexivity.
Qed.
Print Assumptions zesu_integer_array_byte_equality.

Global Instance zesu_integer_array_word_inhabited (base offset : Z)
    (bytes : list (bv 8)) :
  Inhabited
    (RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
      (take 8 (drop (Z.to_nat (base + offset - base)) bytes)))) =
     RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
      (take 8 (drop (Z.to_nat offset) bytes))))).
Proof.
  constructor.
  rewrite (zesu_integer_array_byte_equality base offset bytes).
  reflexivity.
Qed.
Print Assumptions zesu_integer_array_word_inhabited.

(* Finish the exact byte-word image after the integer base cancels. *)
Ltac zesu_finish_integer_word_image :=
  lazymatch goal with
  | |- RVal_Bits ?loaded = RVal_Bits ?expected =>
      progress rewrite zesu_integer_array_byte_equality;
      cbn; reflexivity
  end.

#[export] Hint Resolve zesu_integer_array_byte_equality : core.

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

(* A retained extent identifies a complete prefix without choosing new data. *)
Lemma zesu_take_complete {A : Type} (values : list A) (count : Z) :
  Z.of_nat (length values) = count ->
  firstn (Z.to_nat count) values = values.
Proof.
  intro Hlength. rewrite -Hlength Nat2Z.id. apply firstn_all.
Qed.
Print Assumptions zesu_take_complete.
