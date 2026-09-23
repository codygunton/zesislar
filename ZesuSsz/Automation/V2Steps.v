(* The rule-set v2 steps, dispatched by goal shape.

   Each of these steps changes what the search closes, so each is
   guarded: rule set v1 must keep its outcomes exactly. The guard is a
   class with one instance, in `Switch.v`, which only rule set v2
   imports.

   This tactic is reached from `zesu_run_pass_v2` and from nowhere else.
   It is not in rule set v1's search list, and that is measured: with it
   there, `check-iris` failed three times on
   `WriteSuccessExactByteListsPublicResources.v` at the same line with
   "Timeout!", under three different guards -- four separately guarded
   steps, one alternative with a class lookup, and one alternative that
   matched the goal shape before the class lookup. The cost is the
   alternative itself, on a proof that carries a wall-clock `timeout`,
   not the guard in front of it.

   The shape still comes first inside v2. One `lazymatch` on the goal
   decides whether any of these steps could apply, and only then is the
   switch asked for, so a v2 module pays one failed match on the
   overwhelming majority of goals.

   Each branch asks for its own step's switch, not for the rule set's,
   so a benchmark arm that imports one `Automation/Switches/<step>.v`
   runs that step and no other. *)

Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.LookupReduce.
Require Import ZesuSsz.Automation.CallReturn.
Require Import ZesuSsz.Automation.CallReturnSpecTable.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.CarrierArray.

Ltac zesu_rule_set_v2_steps :=
  lazymatch goal with
  (* C7: the instruction a lookup holds, in the form the search reads. *)
  | |- envs_entails _ (subsume (instr _ _) _ _) =>
      zesu_reduce_instr_lookup_if_enabled
  (* C7: the continuation a returning call leaves. *)
  | |- envs_entails _ ((_ -∗ _ -∗ WPasm _) ∗ True)%I =>
      zesu_enter_call_return_if_enabled
  | |- envs_entails _ ((_ -∗ WPasm _) ∗ True)%I =>
      zesu_enter_call_return_if_enabled
  | |- envs_entails _ ((_ -∗ zesu_ld_spec _ _ _ _) ∗ True)%I =>
      zesu_enter_call_return_spec_table_if_enabled
  (* C3: a sealed bundle, opened for the lookup that failed. *)
  | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) =>
      zesu_open_sealed_for_lookup_if_enabled
  | |- envs_entails _ (find_in_context (FindRegMapsTo _) _) =>
      zesu_open_sealed_for_lookup_if_enabled
  | |- envs_entails _ (@bi_exist _ (li_prod (bv 64) unit) _) =>
      zesu_open_sealed_for_lookup_if_enabled
  (* C1: the trace tail a handover leaves open. *)
  | |- envs_entails _ (@bi_exist _ (li_prod spec _) _) =>
      zesu_close_spec_tail_if_enabled
  (* A split byte array in a transaction carrier handoff. *)
  | |- envs_entails _
      (@bi_exist _ (bv 64) (fun _ => @bi_exist _ Z _)) =>
      zesu_carrier_array_handoff_if_enabled
  end.
