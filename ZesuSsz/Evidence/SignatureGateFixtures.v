From Coq Require Import Lists.List Logic.FunctionalExtensionality ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Compliance.EvmSailAdapter.
Require Import ZesuSsz.Evidence.SignatureGates.

Theorem fixture_false : False -> ReviewedControlType.
Proof. intros; apply reviewed_control. Qed.
Fail Check (@fixture_false : ReviewedControlType).

Theorem fixture_evaluator : (nat -> Prop) -> ReviewedControlType.
Proof. intros; apply reviewed_control. Qed.
Fail Check (@fixture_evaluator : ReviewedControlType).

Theorem fixture_decoder_contract : ReviewedControlType -> ReviewedControlType.
Proof. intros; apply reviewed_control. Qed.
Fail Check (@fixture_decoder_contract : ReviewedControlType).

Definition ReviewedFunctionType : Prop :=
  (fun x : nat => x) = (fun x : nat => x).
Theorem fixture_axiom : ReviewedFunctionType.
Proof.
  unfold ReviewedFunctionType.
  apply functional_extensionality.
  intro x; reflexivity.
Qed.
Check (@fixture_axiom : ReviewedFunctionType).
Print Assumptions fixture_axiom.
Fail Ltac2 Eval exact_axioms 'fixture_axiom (approved_library_axioms ()).

Theorem fixture_changed_domain :
  forall bytes : list nat, bytes <> nil -> bytes = bytes.
Proof. intros; reflexivity. Qed.
Fail Check (@fixture_changed_domain : ReviewedControlType).

Theorem fixture_changed_relation :
  forall bytes : list nat, length bytes = length bytes.
Proof. intros; reflexivity. Qed.
Fail Check (@fixture_changed_relation : ReviewedControlType).

(* These are the unconstrained binders from the inherited adapter and shell. *)
Theorem fixture_inherited_binders :
  forall (runner model inputRef : Type) (mainOk decodeOk : Prop),
  ReviewedControlType.
Proof. intros; apply reviewed_control. Qed.
Fail Check (@fixture_inherited_binders : ReviewedControlType).
