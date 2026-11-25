Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A leftover existential that only pure facts constrain, its spatial rest
   held (ExistsPure.v): the pure statement binds the tuple's components one
   by one, and a proof of it closes the goal. Refused when the spatial rest
   mentions the witness or is not held. *)

Section exists_pure.
Context `{!islaG Sigma} `{!threadG}.

Lemma exists_pure_statement (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z *ₗ bool *ₗ unit, ⌜x.1ₗ = a⌝ ∗ (⌜x.2ₗ = true⌝ ∗ K).
Proof.
  iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun E =>
    constr_eq E (exists (a0 : Z) (b : bool), a0 = a /\ b = true)).
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(exists a, true; split; reflexivity).
Qed.

(* A witness type that is not a tuple: one binder. *)
Lemma exists_pure_single (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z, ⌜x = a⌝ ∗ K.
Proof.
  iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun E => constr_eq E (exists a0 : Z, a0 = a)).
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(exists a; reflexivity).
Qed.

(* The spatial rest mentions the witness. *)
Lemma exists_pure_refused_dependent (P : Z -> iProp Sigma) (a : Z) :
  P a -∗ ∃ x : Z, ⌜x = a⌝ ∗ P x.
Proof.
  iIntros "HP".
  Fail ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun _ => idtac).
  iExists a. iFrame. done.
Qed.

(* The spatial rest is not held (`emp` is no hypothesis). *)
Lemma exists_pure_refused_not_held (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z, ⌜x = a⌝ ∗ K ∗ emp.
Proof.
  iIntros "HK".
  Fail ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun _ => idtac).
  iExists a. iFrame. done.
Qed.
End exists_pure.
