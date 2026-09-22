(* The rule-set v2 steps, dispatched by goal shape.

   Each of these steps changes what the search closes, so each is
   guarded: rule set v1 must keep its outcomes exactly. The guard is a
   class with one instance, in `Switch.v`, which only rule set v2
   imports.

   The dispatch matters as much as the guard. Asking for the class on
   every interpreter step is not free: `check-iris` was green before
   these steps were added and then failed on
   `WriteSuccessExactByteListsPublicResources.v` with "Timeout!", the
   same file at the same line, on a loaded machine and on a quiet one.
   The proof has a wall-clock `timeout` in it and a class lookup per
   step, over a proof that runs for minutes, is enough to spend it.

   So the shape comes first. One `lazymatch` on the goal decides whether
   any of these steps could apply, and only then is the switch asked
   for. For the overwhelming majority of goals the cost is one failed
   match. *)

Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.LookupReduce.
Require Import ZesuSsz.Automation.CallReturn.
Require Import ZesuSsz.Automation.SealedCoverage.

Ltac zesu_rule_set_v2_steps :=
  lazymatch goal with
  (* C7: the instruction a lookup holds, in the form the search reads. *)
  | |- envs_entails _ (subsume (instr _ _) _ _) =>
      zesu_rule_set_v2_on; zesu_reduce_instr_lookup
  (* C7: the continuation a returning call leaves. *)
  | |- envs_entails _ ((_ -∗ _ -∗ WPasm _) ∗ True)%I =>
      zesu_rule_set_v2_on; zesu_enter_call_return
  | |- envs_entails _ ((_ -∗ WPasm _) ∗ True)%I =>
      zesu_rule_set_v2_on; zesu_enter_call_return
  (* C3: a sealed bundle, opened for the lookup that failed. *)
  | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) =>
      zesu_rule_set_v2_on; zesu_open_sealed_for_lookup
  | |- envs_entails _ (find_in_context (FindRegMapsTo _) _) =>
      zesu_rule_set_v2_on; zesu_open_sealed_for_lookup
  | |- envs_entails _ (@bi_exist _ (li_prod (bv 64) unit) _) =>
      zesu_rule_set_v2_on; zesu_open_sealed_for_lookup
  (* C1: the trace tail a handover leaves open. *)
  | |- envs_entails _ (@bi_exist _ (li_prod spec _) _) =>
      zesu_rule_set_v2_on; zesu_close_spec_tail
  end.
