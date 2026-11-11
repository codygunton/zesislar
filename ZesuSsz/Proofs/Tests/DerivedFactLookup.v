Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Record LookupArgs := { lookupFrame : Z }.

(* A folded domain: a record proposition, so no step can split it. Its range
   reaches the solvers only through the registered derivation below. *)
Record LookupDomain (args : LookupArgs) (bytes : list (bv 8)) : Prop := {
  lookup_domain_frame : 96 <= lookupFrame args < 2 ^ 64;
  lookup_domain_length : length bytes = 16%nat
}.

#[local] Instance lookup_domain_derived (args : LookupArgs) (bytes : list (bv 8)) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts (LookupDomain args bytes)
    ((96 <= lookupFrame args < 2 ^ 64) /\ length bytes = 16%nat) :=
  fun H => conj (lookup_domain_frame _ _ H) (lookup_domain_length _ _ H).

(* A load at a cast plus literal constants, inside a byte array owned at the
   Z base frame - 96 + 8. *)
Lemma derived_range_at_lookup `{!islaG Sigma} `{!threadG} (args : LookupArgs) (bytes : list (bv 8)) :
  LookupDomain args bytes ->
  (lookupFrame args - 96 + 8) ↦ₘ∗ bytes -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (lookupFrame args) + BV 64 (2 ^ 64 - 96) + BV 64 8 + BV 64 8)))
    (fun _ => True)%I.
Proof. intros Hdomain. iIntros "Harray". zesu_block2. Qed.

(* The remainder of a wrapped cast sum: the divisibility is a plain fact, and
   the range that keeps the sum in one wrap comes only from the folded domain. *)
Lemma derived_range_remainder `{!islaG Sigma} `{!threadG} (args : LookupArgs) (bytes : list (bv 8)) (R : iProp Sigma) :
  LookupDomain args bytes -> (16 | lookupFrame args) ->
  R -∗ (⌜bv_unsigned (Z_to_bv 64 (lookupFrame args) + BV 64 (2 ^ 64 - 96)) mod 16 = 0⌝ ∗ R).
Proof. intros Hdomain Hdivide. iIntros "HR". zesu_block2. Qed.
