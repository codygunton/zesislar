Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.Diagnostics.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* Without DiagnosticsOn every hook is inert: the stage and refusal hooks
   leave the goal and the context unchanged, and the step hook fails, so a
   search loop goes on to its real alternatives. *)
Ltac diag_off_check := zesu_diag_on.

Lemma refusal_hooks_off (x : Z) (Hx : 0 <= x < 10) : x + 1 <= 11.
Proof.
  Fail diag_off_check.
  Fail zesu_diag_step.
  zesu_diag_stage "test";
  zesu_diag_step_end;
  zesu_diag_refusal "test".
  match goal with |- x + 1 <= 11 => idtac end.
  lia.
Qed.
