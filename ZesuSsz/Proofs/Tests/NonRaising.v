Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Prototypes.NonRaising.

(* A pure goal the finisher closes: closed, not raised. *)
Lemma test_nonraising_closes (n : nat) : n + 0 = n.
Proof. zesu_block_nr. Qed.

(* A pure goal no solver closes: kept as a residual, not raised. *)
Lemma test_nonraising_keeps (P : Prop) : P.
Proof.
  zesu_block_nr.
  lazymatch goal with |- P => idtac | |- _ => fail "the goal changed" end.
Abort.

Lemma test_nonraising_legacy_keeps (P : Prop) : P.
Proof.
  zesu_block_nr_legacy.
  lazymatch goal with |- P => idtac | |- _ => fail "the goal changed" end.
Abort.
