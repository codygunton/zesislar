Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A stack pointer that is a record projection, not a variable: no
   hypothesis `sp : bv 64` gives its type range. *)
Record frameArgs := { frameStack : bv 64 }.

(* stdpp's saturation alone leaves `bv_unsigned (frameStack args)` unbounded
   above; the equation needs `< 2^64`. *)
Lemma type_range_saturation (args : frameArgs) :
  512 <= bv_unsigned (frameStack args) ->
  bv_unsigned (bv_add (frameStack args) (BV 64 18446744073709551216)) =
    bv_unsigned (frameStack args) - 400.
Proof. intros Hlow. stdpp.bitvector.tactics.bv_solve. Qed.

(* The normal form's cast range gets the same bound. *)
Lemma type_range_cast (args : frameArgs) :
  512 <= bv_unsigned (frameStack args) ->
  bv_unsigned (bv_add (frameStack args) (BV 64 18446744073709551224)) =
    bv_unsigned (frameStack args) - 392.
Proof.
  intros Hlow.
  ZesuSsz.Automation2.BvLinear.zesu_bv_linear_with ltac:(zesu_lia).
Qed.

(* The goal scan adds the range of a non-variable root always, of a variable
   root only when asked (`true`); with `false` stdpp's own saturation covers
   the variable. *)
Lemma type_range_variable_guard (args : frameArgs) (sp : bv 64) :
  bv_unsigned sp + bv_unsigned (frameStack args) = bv_unsigned (frameStack args) + bv_unsigned sp.
Proof.
  ZesuSsz.Automation2.BvLinear.zesu_bv_ranges_goal_with false.
  lazymatch goal with
  | _ : -1 < bv_unsigned (frameStack args) < bv_modulus 64 |- _ => idtac
  end.
  lazymatch goal with
  | _ : -1 < bv_unsigned sp < bv_modulus 64 |- _ => fail
  | _ => idtac
  end.
  ZesuSsz.Automation2.BvLinear.zesu_bv_ranges_goal_with true.
  lazymatch goal with
  | _ : -1 < bv_unsigned sp < bv_modulus 64 |- _ => idtac
  end.
  apply Z.add_comm.
Qed.

Print Assumptions type_range_saturation.
