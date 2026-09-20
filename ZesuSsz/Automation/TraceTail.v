(* C1: the trace tail a call returns with.

   The corpus calls this the line every segment proof repeats. A call
   returns with its events still open, so the block is asked for a spec `x`
   such that the events it produced, followed by `x`, stay inside the
   events the caller promised:

     ∃ x : spec *ₗ …, ⌜scons_snap event accept x ⊆ scons event tail⌝ ∗ …

   The witness is always the caller's tail, the second argument of the
   `scons` on the right; and once `x` is that tail the inclusion holds
   because `scons_snap` only adds a constraint on the snapshot that `scons`
   does not make. About 70 proofs and 300 hand lines in the backlog
   (rows 8, 12, 13, 16, 18) are this one step.

   `spec_solver` is Islaris's own solver for these (theories/spec.v); the
   hand line spells it out as
   `unfold subseteq, spec_subseteq, scons, scons_snap; naive_solver`. *)

Require Export ZesuSsz.Automation.Finish.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From lithium Require Import pure_definitions.

Section trace_tail_prod.
  Context {Sigma : gFunctors}.

  (* Lithium's `liExist` ends with `fail "not handled by liExist"` for a
     `li_prod` existential whose body uses the variable
     (lithium/interpreter.v). Every call that returns an open trace leaves
     exactly that shape, `∃ x : spec *ₗ …, ⌜… x.1ₗ ⊆ …⌝ ∗ … x.1ₗ`, so the
     search stops there and the author writes the witness by hand. Splitting
     the product into ordinary existentials hands the goal back to Lithium,
     which instantiates each component with an evar as usual. *)
  Lemma tac_zesu_li_prod_exist {A B} Delta (Phi : li_prod A B → iProp Sigma) :
    envs_entails Delta (∃ (a : A) (b : B), Phi (a, b)ₗ) →
    envs_entails Delta (∃ x : li_prod A B, Phi x).
  Proof.
    rewrite envs_entails_unseal => Hgoal. etrans; [exact Hgoal|].
    iIntros "(%a & %b & H)". by iExists (a, b)ₗ.
  Qed.
End trace_tail_prod.

Section trace_tail.

  Lemma zesu_scons_snap_subseteq_scons (event : seq_event)
      (accept : seq_snapshot -> Prop) (tail : spec) :
    scons_snap event accept tail ⊆ scons event tail.
  Proof. spec_solver. Qed.

  Lemma zesu_scons_subseteq_scons (event : seq_event) (tail : spec) :
    scons event tail ⊆ scons event tail.
  Proof. spec_solver. Qed.

End trace_tail.

(* The witness comes from the right of the inclusion. Both events are
   compared syntactically and the open spec must be an evar: a `unify` on
   these terms runs a conversion check over the whole event history, which
   on the suffix-entry segment did not finish in forty minutes. The tactic
   fails when the shape is not this one, and the finisher moves on. *)
(* Only when Lithium has already refused: this sits last in the search
   list, so it never pre-empts `liExist`'s own handling of a product. *)
Ltac zesu_open_li_prod :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod _ _) _) =>
      notypeclasses refine (tac_zesu_li_prod_exist _ _ _); red_li_prod
  end.

Ltac zesu_finish_trace_tail :=
  lazymatch goal with
  | |- scons_snap ?event _ ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_snap_subseteq_scons _ _ _)
  | |- scons ?event ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_subseteq_scons _ _)
  end.

(* Fill the finisher hook now that the rule exists. *)
Ltac zesu_finish_trace_tail_hook ::= zesu_finish_trace_tail.

(* `zesu_open_li_prod` is deliberately not wired into the search list; see
   the hook's comment in Finish.v. A proof may still call it by hand. *)
