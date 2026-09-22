(* C1: the trace tail a handover leaves open.

   A block that calls out, or writes to MMIO, hands the rest of its trace
   to the continuation. Lithium states that as an existential over a
   `li_prod` whose first component is a `spec`, and the only thing that
   fixes it is the inclusion beside it:

     ∃ x : spec *ₗ (), ⌜E x.1ₗ ⊆ DECLARED⌝ ∗ … ∗ instr_pre ret (… x.1ₗ) …

   The hand proof answers this with `liInst`, naming the tail: five such
   lines in the post-withdrawals draft alone, one per call, each of them
   a name the writer had to find in the trace definition.

   Nothing has to be found. `E x.1ₗ ⊆ DECLARED` has a canonical answer
   whenever `DECLARED` reduces to `E tail`: take `x.1ₗ := tail` and the
   inclusion is reflexivity. So the rule leaves the tail as an evar and
   reduces the declared spec until the two sides meet. `reflexivity`
   does the unification; the reduction is `unfold` of the declared
   spec's head, which is how a project's trace definitions are layered.

   The rule is bounded and it never guesses: if the reduction does not
   reach the shape, the tactic fails and the stall stays a ticket. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

(* One delta step on the right of the inclusion. A sealed spec has no
   delta step, so the rule stops there rather than opening it: a seal on
   a trace is a statement that the trace is not meant to be looked
   inside. *)
Ltac zesu_unfold_declared_spec :=
  lazymatch goal with
  | |- _ ⊆ ?declared =>
      let head := get_head declared in
      progress unfold head
  end.

(* Delta steps and a weak head reduction, and `reflexivity` after each,
   because the moment the two sides meet the evar is the tail.

   `cbn` is deliberately not in the list. Measured on post-withdrawals:
   `cbn` does make progress and `reflexivity` still fails, because the
   declared spec's descriptor list is `drop (length … + …) (map …)` over
   abstract witness fields and no reduction reaches the write at its
   head. All `cbn` buys there is a large term and ten seconds of every
   stall. A spec that needs it needs a lemma instead, stated at the
   chain end. *)
Ltac zesu_spec_tail_reflexivity :=
  solve [repeat first
    [reflexivity
    |zesu_unfold_declared_spec
    |progress hnf]].

Ltac zesu_close_spec_tail :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      iExists (_, tt)ₗ
  | |- envs_entails _ (@bi_exist _ (li_prod spec _) _) =>
      iExists (_, _)ₗ
  end;
  iSplit; [iPureIntro; timeout 5 zesu_spec_tail_reflexivity |].

Ltac zesu_close_spec_tail_if_enabled :=
  zesu_rule_set_v2_on; zesu_close_spec_tail.
