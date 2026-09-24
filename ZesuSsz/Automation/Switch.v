(* Every rule set v2 step at once.

   `PureFacts.v` declares `ZesuRuleSetV2`, which selects
   `zesu_run_pass_v2`, and each step declares a class of its own. This
   file is the union: it imports the five `Switches/` modules, so
   importing it turns on the whole set. `Automation/Sets/v2.v` imports
   it, and a module that does not sees one failed class lookup per pass
   and nothing else.

   The guard is not caution for its own sake. The first `check-iris`
   with the C6 arithmetic step always on failed two merged proofs: one
   because the step closed the goal a hand line was written for, and one
   because the step spent the proof's timeout budget. A stronger
   automation is still a change, and row 6 owes a demonstration that
   v1's outcomes are identical.

   To measure one rule instead of all of them, import one
   `Switches/<step>.v`. That is what `tools/det/bench_rules.py` does,
   one arm per rule. *)

Require Export ZesuSsz.Automation.Switches.WitnessArith.
Require Export ZesuSsz.Automation.Switches.SpecTail.
Require Export ZesuSsz.Automation.Switches.LookupReduce.
Require Export ZesuSsz.Automation.Switches.CallReturn.
Require Export ZesuSsz.Automation.Switches.SealedOpen.
Require Export ZesuSsz.Automation.Switches.FourWordScratch.
