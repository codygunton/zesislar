From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A successor binder with no resource, packed into Lithium's tuple (its name
   gone), fixed only by a named equation: the witness is the equation's term
   (`NamedEquations.zesu_named_equation_witness`). *)
Section named_equation_witness.
Context `{!islaG Sigma} `{!threadG}.

Lemma named_equation_witness_fires (c w : bv 64) (P : bv 64 -> Prop) (R : iProp Sigma) :
  P c ->
  R -∗ ∃ x : bv 64 *ₗ (), ⌜P x.1ₗ⌝ ∗ ⌜zesu_named_eq (bv_sub c w) (bv_sub x.1ₗ w)⌝ ∗ R.
Proof.
  iIntros (HP) "HR".
  ZesuSsz.Automation2.NamedEquations.zesu_named_equation_witness.
  iSplitR; [iPureIntro; exact HP|].
  iSplitR; [iPureIntro; exact (zesu_named_eq_intro _ _ eq_refl)|].
  iExact "HR".
Qed.

(* Guard: a binder that a resource fixes is left to the resource. *)
Lemma named_equation_witness_resource (a : Z) (c : bv 64) :
  a ↦ₘ c -∗ ∃ x : bv 64 *ₗ (), ⌜zesu_named_eq c x.1ₗ⌝ ∗ a ↦ₘ x.1ₗ.
Proof.
  iIntros "Ha".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_equation_witness.
  iExists (li_pair c tt). iSplitR; [iPureIntro; exact (zesu_named_eq_intro _ _ eq_refl)|].
  iExact "Ha".
Qed.

(* Guard: no named equation sets the binder. *)
Lemma named_equation_witness_unset (c : bv 64) (P : bv 64 -> Prop) (R : iProp Sigma) :
  P c ->
  R -∗ ∃ x : bv 64 *ₗ (), ⌜P x.1ₗ⌝ ∗ R.
Proof.
  iIntros (HP) "HR".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_equation_witness.
  iExists (li_pair c tt). iSplitR; [iPureIntro; exact HP|]. iExact "HR".
Qed.
End named_equation_witness.

Print Assumptions named_equation_witness_fires.
