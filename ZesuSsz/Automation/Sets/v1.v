(* Rule set v1: the automation the corpus was measured against.

   `Automation/All.v` is the entry point every proof imports, and it moves
   as rules land. A measurement needs a name that does not move, so a set
   is a module that exports a fixed list. v1 is the list as it stood when
   this branch opened: every proof in the repository builds against it,
   and it is the baseline both benchmark arms are compared to.

   v1 does not include the opt-in rules. They are in `v2.v`. *)

Require Export InstrSpecs.Lookup.
Require Export InstrSpecs.Machine.
Require Export InstrSpecs.Specs.
Require Export ZesuSsz.Automation.Calls.
Require Export ZesuSsz.Automation.InstrPre.
Require Export ZesuSsz.Automation.Finish.
Require Export ZesuSsz.Automation.Rewrites.
Require Export ZesuSsz.Automation.Hooks.
Require Export ZesuSsz.Automation.UninitRegions.
Require Export ZesuSsz.Automation.NatBitvectors.
Require Export ZesuSsz.Automation.ArrayPacking.
