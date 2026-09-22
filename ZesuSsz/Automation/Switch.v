(* Turn on the steps that change what rule set v1 closes.

   `PureFacts.v` declares `ZesuRuleSetV2` and every step of that kind
   asks for it; this file is the only instance. A module that does not
   import it, directly or through `Automation/Sets/v2.v`, sees one failed
   class lookup per step and nothing else.

   The guard is not caution for its own sake. The first `check-iris` with
   the C6 arithmetic step always on failed two merged proofs: one because
   the step closed the goal a hand line was written for, and one because
   the step spent the proof's timeout budget. A stronger automation is
   still a change, and row 6 owes a demonstration that v1's outcomes are
   identical. *)

Require Import ZesuSsz.Automation.PureFacts.

Global Instance zesu_rule_set_v2_instance : ZesuRuleSetV2 := I.
