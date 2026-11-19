Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith.
Local Open Scope Z_scope.

(* `unLET` and the finisher's metadata-preserving form clear the local
   definitions nothing mentions, then unfold the others. Unused definitions
   that depend on each other go in one pass, newest first. *)
Lemma unlet_clears_unused (x : Z) : x = x.
Proof.
  pose (base := x + 1).
  pose (unused := base * 2).
  pose (unused2 := unused + base).
  pose (used := x).
  change (used = x).
  unLET.
  Fail (clear base). Fail (clear unused). Fail (clear unused2). Fail (clear used).
  lazymatch goal with |- x = x => reflexivity end.
Qed.

Lemma unlet_metadata_clears_unused (x : Z) : x = x.
Proof.
  pose (unused := x + 1).
  pose (used := x).
  change (used = x).
  ZesuSsz.Automation2.Hooks.zesu_unlet_preserving_witness_metadata.
  Fail (clear unused). Fail (clear used).
  lazymatch goal with |- x = x => reflexivity end.
Qed.

(* A definition that a kept hypothesis mentions is unfolded, not lost. *)
Lemma unlet_unfolds_used (x : Z) (P : Z -> Prop) (Hp : P (x + 1)) : P (x + 1).
Proof.
  pose (next := x + 1).
  pose (unused := next * 2).
  change (P next) in Hp.
  unLET.
  Fail (clear next). Fail (clear unused).
  exact Hp.
Qed.
