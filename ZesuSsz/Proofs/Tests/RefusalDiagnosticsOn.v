Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.DiagnosticsOn.
From Coq Require Import ZArith.ZArith Lia.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* With DiagnosticsOn the hooks print but never change the proof: the step
   hook still fails, and the stage and refusal hooks keep the goal and the
   context. *)
Ltac diag_on_check := zesu_diag_on.

Ltac2 diag_prop_count () :=
  List.length (List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => Constr.equal (Constr.type typ) constr:(Prop)
    | Some _ => false
    end) (Control.hyps ())).

Lemma refusal_hooks_on (x : Z) (Hx : 0 <= x < 10) (Hy : 0 < 1) : x + 1 <= 11.
Proof.
  diag_on_check.
  Fail zesu_diag_step.
  zesu_diag_stage ("test"%string);
  zesu_diag_step_end;
  zesu_diag_refusal ("test"%string).
  match goal with |- x + 1 <= 11 => idtac end.
  ltac2:(if Int.equal (diag_prop_count ()) 2 then () else Control.throw (Tactic_failure None)).
  lia.
Qed.
