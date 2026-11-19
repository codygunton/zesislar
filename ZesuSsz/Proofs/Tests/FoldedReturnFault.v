Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A function's folded precondition: a domain predicate whose body is a tree
   of conjunctions. The return target's range and alignment are only inside. *)
Definition folded_return_domain (R : Z) : Prop :=
  (0 <= R /\ R < 2 ^ 64) /\ R mod 4 = 0.

(* The same tree without the alignment conjunct. *)
Definition folded_return_range (R : Z) : Prop := 0 <= R /\ R < 2 ^ 64.

(* The fault branch is refuted after the folded precondition is opened; the
   refutation alone (the step before this rule) needs the facts unfolded. *)
Lemma folded_return_fault_entry (R : Z) :
  folded_return_domain R ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  False.
Proof.
  intros Hdomain Hfault.
  Fail solve [zesu_refute_aligned_return_fault_core].
  solve [unshelve zesu_liAStep].
Qed.

Lemma folded_return_fault_wrapper (R : Z) :
  folded_return_domain R ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  False.
Proof.
  intros Hdomain Hfault.
  Fail solve [zesu_refute_aligned_return_fault_core].
  solve [zesu_refute_aligned_return_fault].
Qed.

(* Unfolded facts keep the original path. *)
Lemma folded_return_fault_plain (R : Z) :
  0 <= R -> R < 2 ^ 64 -> R mod 4 = 0 ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  False.
Proof.
  intros Hlower Hupper Haligned Hfault.
  solve [zesu_refute_aligned_return_fault_core].
Qed.

(* A folded precondition without the alignment does not refute the branch. *)
Lemma folded_return_fault_unaligned (R : Z) :
  folded_return_range R ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  True.
Proof.
  intros Hrange Hfault.
  Fail solve [zesu_refute_aligned_return_fault].
  exact I.
Qed.

(* The folded precondition is opened only on a fault branch. *)
Lemma folded_return_no_fault (R : Z) :
  folded_return_domain R -> R mod 4 = 0.
Proof.
  intros Hdomain.
  Fail zesu_refute_aligned_return_fault.
  exact (proj2 Hdomain).
Qed.

Print Assumptions folded_return_fault_entry.
Print Assumptions folded_return_fault_wrapper.

(* Without the folded-precondition opening, the step does not close the
   branch. *)
#[local] Ltac ZesuSsz.Automation2.Hooks.zesu_open_folded_facts ::=
  fail "folded precondition opening disabled".

Lemma folded_return_fault_needs_opening (R : Z) :
  folded_return_domain R ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  True.
Proof.
  intros Hdomain Hfault.
  Fail assert False by solve [zesu_refute_aligned_return_fault].
  Fail assert False by solve [unshelve zesu_liAStep].
  exact I.
Qed.
