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
Require Export ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Automation2.InstrPre.
Require Export ZesuSsz.Automation2.Finish.
Require Export ZesuSsz.Automation2.Rewrites.
Require Export ZesuSsz.Automation2.Hooks.
Require Export ZesuSsz.Automation2.UninitRegions.
Require Export ZesuSsz.Automation2.NatBitvectors.
Require Export ZesuSsz.Automation2.ArrayPacking.

#[export] Instance zesu_explicit_v1 : ZesuSsz.Automation2.PureFacts.ZesuRuleSetV1 := I.
