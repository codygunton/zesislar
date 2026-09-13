Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

(* Reduce an extraction hypothesis before solving pointer arithmetic. *)
Ltac zesu_alignment :=
  lazymatch goal with
  | |- bv_extract _ _ _ = _ => idtac
  end;
  match goal with
  | Halign : bv_extract 0 _ ?pointer = _ |- _ =>
      lazymatch goal with
      | |- context[pointer] =>
          solve [clear -Halign; bv_simplify_arith Halign; bv_solve]
      end
  end.
