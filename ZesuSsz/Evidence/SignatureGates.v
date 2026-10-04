From Coq Require Import Lists.List.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Evidence.SignatureAxiomAllowlist.

Declare ML Module "zesu-signature-gates.plugin".

Ltac2 @ external exact_axioms : constr -> constr list -> unit :=
  "zesu-signature-gates.plugin" "exact_axioms".

(* The reviewed type in this initial gate is a closed control fixture.
   Add each public compliance theorem only after its complete type is reviewed. *)
Definition ReviewedControlType : Prop :=
  forall bytes : list nat, bytes = bytes.

Theorem reviewed_control : ReviewedControlType.
Proof. unfold ReviewedControlType; intros; reflexivity. Qed.

Check (@reviewed_control : ReviewedControlType).
Print Assumptions reviewed_control.
Ltac2 Eval exact_axioms 'reviewed_control (approved_library_axioms ()).
