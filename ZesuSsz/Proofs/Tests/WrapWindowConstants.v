From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

(* A callee frame 16 bytes below a word's -400 offset, inside a 112-byte
   region at w - 512: the normalized split offset is 96, not 2^64 + 96. *)
Goal forall (w : bv 64), exists m, m = 96%Z /\
  (forall x, bv_wrap 64 m = x -> block bv_wrap 64%N
    ((bv_unsigned (bv_add w (BV 64 18446744073709551216)) - 16) - (bv_unsigned w - 400 - 112))%Z = x).
Proof. intros w. eexists. split; cycle 1; [solve_normalize_bv_wrap | reflexivity]. Qed.

(* Beyond 64 KiB below 2^64 a constant keeps its unsigned form. *)
Goal forall (w : bv 64), (exists m, m = (-69984)%Z /\
  (forall x, bv_wrap 64 m = x -> block bv_wrap 64%N
    ((bv_unsigned (bv_add w (BV 64 18446744073709481616)) - 16) - (bv_unsigned w - 70000 - 112))%Z = x)) \/ True.
Proof.
  intros w.
  Fail (left; eexists; split; cycle 1; [solve_normalize_bv_wrap | reflexivity]).
  right. exact I.
Qed.
