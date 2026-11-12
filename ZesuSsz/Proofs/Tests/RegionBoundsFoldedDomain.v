From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The region bound solver opens a folded domain predicate. The range of
   the frame pointer exists only inside the predicate, as in the premise
   of `find_mem_region_uninit` for a store below a pointer whose bound a
   contract's domain predicate holds. *)
Record region_args := { region_cursor : Z; region_length : Z }.

Definition region_domain (args : region_args) : Prop :=
  64 <= region_cursor args /\ region_cursor args < 2 ^ 64.

Lemma region_bounds_opens_folded_domain (args : region_args) :
  region_domain args ->
  (region_cursor args - 64 <=
     bv_unsigned (Z_to_bv 64 (region_cursor args) + Z_to_bv 64 18446744073709551608) <
     region_cursor args - 64 + 64) \/
  region_cursor args - 64 =
    bv_unsigned (Z_to_bv 64 (region_cursor args) + Z_to_bv 64 18446744073709551608).
Proof. intros Hdomain. ZesuSsz.Automation2.UninitRegions.zesu_region_bounds. Qed.

(* A predicate that does not bound the pointer from below still refuses
   the region. *)
Definition region_upper (args : region_args) : Prop :=
  0 <= region_length args /\ region_cursor args < 2 ^ 64.

Lemma region_bounds_refuses_without_bound (args : region_args) : region_upper args -> True.
Proof.
  intros Hupper.
  assert_fails (assert ((region_cursor args - 64 <=
     bv_unsigned (Z_to_bv 64 (region_cursor args) + Z_to_bv 64 18446744073709551608) <
     region_cursor args - 64 + 64) \/
    region_cursor args - 64 =
     bv_unsigned (Z_to_bv 64 (region_cursor args) + Z_to_bv 64 18446744073709551608))
    by ZesuSsz.Automation2.UninitRegions.zesu_region_bounds).
  exact I.
Qed.
