From Coq Require Import ZArith.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The assembling source route keeps the first match of the requested facts.
   Below, the spatial atom [R] mentions every witness, so the facts form one
   uncommitted segment whose ten shared evars each have three candidates.
   No candidate closes [R]: without the commit, the route retries all 3^10
   witness combinations before it refuses. *)

Ltac source_assembled_route :=
  iStartProof;
  ZesuSsz.Automation2.Finish.zesu_finish_source_assembled
    ltac:(fun requested =>
      ZesuSsz.Automation2.SourceFactMatching.zesu_source_check_fixed_tree requested).

Section source_assembled_route.
Context {Σ : gFunctors}.

Lemma source_assembled_route_refuses_once
    (R : list Z -> iProp Σ) (v1 v2 v3 : Z)
    (Hv1 : v1 < 10) (Hv2 : v2 < 10) (Hv3 : v3 < 10) : True.
Proof.
  Fail assert (Hpackage : ⊢ ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Z,
      ⌜a1 < 10⌝ ∗ ⌜a2 < 10⌝ ∗ ⌜a3 < 10⌝ ∗ ⌜a4 < 10⌝ ∗ ⌜a5 < 10⌝ ∗
      ⌜a6 < 10⌝ ∗ ⌜a7 < 10⌝ ∗ ⌜a8 < 10⌝ ∗ ⌜a9 < 10⌝ ∗ ⌜a10 < 10⌝ ∗
      R [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10])
    by source_assembled_route.
  exact I.
Qed.

(* Inside the segment the matcher still backtracks: [a] first meets [u],
   which [P a] refuses, and then [v]. The first full match passes. *)
Lemma source_assembled_route_first_match
    (P : Z -> Prop) (u v : Z) (Hu : u < 10) (Hv : v < 10) (HP : P v) :
  ⊢@{iPropI Σ} ∃ a : Z, ⌜a < 10⌝ ∗ ⌜P a⌝.
Proof. source_assembled_route. Qed.

End source_assembled_route.
