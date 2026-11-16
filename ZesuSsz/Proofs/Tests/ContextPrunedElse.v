From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The closer runs on the pruned context first. *)
Lemma pruned_else_pruned_closes (x z : Z) (Hx : 0 < x) (Hz : z = 1) : 0 < x.
Proof.
  ZesuSsz.Automation2.ContextCollection.zesu_context_pruned_else ltac:(fail) ltac:(exact Hx).
Qed.

(* The prune cleared `Hz`, so the closer that needs it fails on the pruned
   context; `whole` then runs on the whole context. *)
Lemma pruned_else_whole_after_clear (x z : Z) (Hx : 0 < x) (Hz : z = 1) : 0 < x.
Proof.
  ZesuSsz.Automation2.ContextCollection.zesu_context_pruned_else
    ltac:(let _ := constr:(Hz) in exact Hx) ltac:(let _ := constr:(Hz) in exact Hx).
Qed.

(* The prune cleared nothing: the pruned attempt already ran on the whole
   context, so `whole` is skipped. *)
Lemma pruned_else_skips_whole (x : Z) (Hx : 0 < x) : 0 < x.
Proof.
  Fail ZesuSsz.Automation2.ContextCollection.zesu_context_pruned_else ltac:(exact Hx) ltac:(fail).
  exact Hx.
Qed.
