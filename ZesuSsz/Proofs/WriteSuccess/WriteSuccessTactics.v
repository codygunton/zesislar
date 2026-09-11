Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Ltac close_infeasible_bv_branches :=
  match goal with
  | Hneq : ?left ≠ ?right |- _ =>
      try solve [iExFalso; iPureIntro; apply Hneq; bv_solve]
  | _ : _ = false |- _ => try solve [iExFalso; iPureIntro; bv_solve]
  | _ : false = _ |- _ => try solve [iExFalso; iPureIntro; bv_solve]
  | _ => idtac
  end.

