(** Bridge lemmas between Sail's bitvector idioms and [bv_solve].

    Copy these from islaris-tutorial. They should be upstream in islaris
    (every user hits the same encodings), but they are not. *)
Require Import isla.isla.
Require Import isla.riscv64.riscv64.

(** [bltu]: unsigned compare rendered as signed compare on 128-bit
    zero-extensions. *)
Lemma bv_zero_extend_128_lt (x y : bv 64) :
  bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y)
  ↔ bv_unsigned x < bv_unsigned y.
Proof. bv_solve. Qed.

(** [ld]: 64-bit load into 64-bit register, rendered as sign extension to
    64 bits — the identity. *)
Lemma bv_sign_extend_64_unsigned (x : bv 64) :
  bv_unsigned (bv_sign_extend 64 x) = bv_unsigned x.
Proof. bv_solve. Qed.

(** Tactic that rewrites Sail's comparison idioms into forms [bv_solve]
    can close. Extend this as you encounter new idioms. *)
Ltac normalise_sail_compare :=
  try rewrite bv_zero_extend_128_lt;
  try rewrite bv_sign_extend_64_unsigned.
