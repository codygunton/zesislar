Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.ResidualExport.
From Coq Require Import ZArith.ZArith Lia.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* The residual tier on a goal whose conclusion mentions local definitions.
   A registered lemma states the conclusion with the definitions unfolded
   (the exported form); the discrimination net treats a local definition in
   the goal as a rigid symbol, so the tier unfolds the definitions in the
   conclusion before its second try. *)
Lemma residual_tier_local_definition_lemma :
  forall (x : Z) (Hx : 0 <= x), 0 < (x + 1) * 2 + 3.
Proof. intros; lia. Qed.
#[local] Hint Resolve residual_tier_local_definition_lemma : zesu_residual.

(* Nested definitions: the second mentions the first. *)
Lemma residual_tier_nested_definitions (x : Z) (Hx : 0 <= x) :
  let first := x + 1 in let second := first * 2 in 0 < second + 3.
Proof.
  intros first second.
  ResidualLemmas.zesu_residual_lemma.
Qed.

(* A premise that mentions a local definition still matches by assumption. *)
Lemma residual_tier_definition_in_premise (x : Z) :
  let shifted := x in 0 <= shifted -> let first := x + 1 in 0 < first * 2 + 3.
Proof.
  intros shifted Hshifted first.
  ResidualLemmas.zesu_residual_lemma.
Qed.

(* The exported statement of such a goal is the registered lemma's
   statement: the tier and the exporter unfold local definitions the same
   way. *)
Lemma residual_tier_export_form (x : Z) (Hx : 0 <= x) :
  let first := x + 1 in let second := first * 2 in 0 < second + 3.
Proof.
  intros first second.
  ltac2:(
    let (facts, _, _) := zesu_export_reach 2048 in
    let (statement, _) := zesu_export_statement facts in
    if Constr.equal statement constr:(forall (x : Z) (Hx : 0 <= x), 0 < (x + 1) * 2 + 3)
    then () else Control.throw (Tactic_failure None)).
  ResidualLemmas.zesu_residual_lemma.
Qed.

(* A goal without local definitions behaves as before, and the tier still
   fails at once when no lemma matches. *)
Lemma residual_tier_plain_goal (x : Z) (Hx : 0 <= x) : 0 < (x + 1) * 2 + 3.
Proof. ResidualLemmas.zesu_residual_lemma. Qed.

Lemma residual_tier_no_matching_lemma (x : Z) (Hx : 0 <= x) : let first := x + 1 in 0 < first * 5.
Proof.
  intros first.
  Fail ResidualLemmas.zesu_residual_lemma.
  unfold first; lia.
Qed.
