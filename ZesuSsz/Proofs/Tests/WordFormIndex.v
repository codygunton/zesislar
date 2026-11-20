From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A frame load whose address is a closed-offset chain on an integer root
   under `Z_to_bv`, against a base on the same integer: the index is a
   literal once the order facts on the root rule out a wrap. *)
Goal forall (sp : Z) (bytes : list (bv 8)) value,
  4096 <= sp < 4294967296 ->
  bytes !! Z.to_nat ((bv_unsigned (Z_to_bv 64 sp + BV 64 18446744073709551520 +
    BV 64 40) - (sp - 96 + 8)) `div` 1) = Some value ->
  bytes !! 32%nat = Some value.
Proof.
  intros sp bytes value Hsp Hlookup.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact Hlookup.
Qed.

(* The same read under `take`/`drop`, the form the successor states. *)
Goal forall (sp : Z) (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  4096 <= sp < 4294967296 -> P (take 2 (drop 32 bytes)) ->
  P (take 2 (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 sp + BV 64 18446744073709551520 +
    BV 64 40) - (sp - 96 + 8))) bytes)).
Proof.
  intros sp bytes P Hsp HP.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact HP.
Qed.

(* Without the order facts the address may wrap: no rewrite. *)
Goal forall (sp : Z) (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  P (take 2 (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 sp + BV 64 18446744073709551520 +
    BV 64 40) - (sp - 96 + 8))) bytes)) -> True.
Proof.
  intros sp bytes P HP.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact I.
Qed.

(* An index that is integer arithmetic over one root. *)
Goal forall (sp : Z) (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  P (drop 16 bytes) -> P (drop (Z.to_nat (sp + 24 - (sp - 96 + 104))) bytes).
Proof.
  intros sp bytes P HP.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact HP.
Qed.

(* A negative integer index is not a literal: no rewrite. *)
Goal forall (sp : Z) (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  P (drop (Z.to_nat (sp - (sp + 8))) bytes) -> True.
Proof.
  intros sp bytes P HP.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact I.
Qed.

(* Every `drop` is tried, not only the first: the first index here has no
   root. *)
Goal forall (n sp : Z) (bytes : list (bv 8)) (P : list (bv 8) -> list (bv 8) -> Prop),
  4096 <= sp < 4294967296 -> P (drop (Z.to_nat n) bytes) (drop 32 bytes) ->
  P (drop (Z.to_nat n) bytes) (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 sp + BV 64 18446744073709551520 +
    BV 64 40) - (sp - 96 + 8))) bytes).
Proof.
  intros n sp bytes P Hsp HP.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact HP.
Qed.
