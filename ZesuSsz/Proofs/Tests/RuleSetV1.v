(* Which pass a module runs is decided by what it imports.

   `zesu_run_pass` in `Automation/Finish.v` asks once per pass for a
   `ZesuRuleSetV2` instance: with one it runs `zesu_run_pass_v2`, which
   is v1's search list plus `zesu_rule_set_v2_steps`; without one it
   runs `zesu_run_pass_v1`, which is the list every merged proof in this
   repository was built against.

   This module imports the v2 machinery by name -- the classes and the
   step tactic -- and not the instance that turns it on, which is the
   case every merged proof is in. So the switch must not resolve and the
   step must refuse. `RuleSetV2.v` beside it is the other half. *)

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.V2Steps.
Require Import isla.riscv64.riscv64.

Lemma test_rule_set_v1_selected : True.
Proof.
  tryif zesu_rule_set_v2_on
  then fail "rule set v2 is not imported and its switch still resolves"
  else exact I.
Qed.
Print Assumptions test_rule_set_v1_selected.

Lemma test_rule_set_v1_steps_off : True.
Proof.
  tryif zesu_rule_set_v2_steps
  then fail "a rule set v2 step ran in a rule set v1 module"
  else exact I.
Qed.
Print Assumptions test_rule_set_v1_steps_off.
