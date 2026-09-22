(* One rule of rule set v2 and no other: the C6 arithmetic a folded hypothesis hides.

   A benchmark arm measures one rule. `Automation/Switch.v` turns every
   v2 step on at once, which answers what rule set v2 costs and not what
   this rule buys, so every step of this kind has a class of its own and
   this file is its only instance.

   `ZesuRuleSetV2` comes with it, because that is what puts
   `zesu_run_pass` on rule set v2's search list at all. With this file
   imported and nothing else from v2, the pass runs v1's alternatives
   plus the one step below. *)

Require Import ZesuSsz.Automation.PureFacts.


Global Instance zesu_switch_witness_arith_set : ZesuRuleSetV2 := I.
Global Instance zesu_switch_witness_arith : ZesuStepWitnessArith := I.
