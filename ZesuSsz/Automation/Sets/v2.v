(* Rule set v2: v1 plus the rules this branch built.

   Each of these is sound and tested, and each was measured on both
   benchmark baselines before it was written down here. They are not in
   `Automation/All.v`, because installing a rule everywhere is a
   different decision from having one: `WordArrayBytes.v` is sound and
   clears the stall it was written for, and installing it breaks a
   merged proof for a reason worth recording rather than working around.

   A generated module imports this set. A merged module keeps v1 until
   its own measurement says otherwise. The demonstration the bundle owes
   is that v1 modules have zero changed outcomes. *)

Require Export ZesuSsz.Automation.Sets.v1.

(* C1: the trace tail of a `scons`/`scons_snap` handover.
   Lemmas, and the hook entries that use them, are in `Hooks.v`. *)
Require Export ZesuSsz.Automation.TraceTailLemmas.

(* C6 and the arithmetic a folded hypothesis hides. `Switch.v` is the
   one instance that turns every such step on; without it each step is a
   failed class lookup and v1's outcomes are unchanged. *)
Require Export ZesuSsz.Automation.PureFacts.
Require Export ZesuSsz.Automation.Switch.
Require Export ZesuSsz.Automation.SpecPrefix.
Require Export ZesuSsz.Automation.LookupReduce.
Require Export ZesuSsz.Automation.CallReturn.
Require Export ZesuSsz.Automation.V2Steps.

(* C3: open a sealed predicate lazily, and only the one that holds the
   address. *)
Require Export ZesuSsz.Automation.SealedCoverage.

(* C4: let the search find a specification in the spec table.

   Careful: the table answers a load instruction with `zesu_ld_spec`,
   whose precondition asks for a bare `↦ₘ` word. A block that loads out
   of an array cannot meet that, and without the table the same
   instruction runs its Isla trace and Islaris's own `MKArray` branch
   handles it. A segment that reads from a stack array wants
   `StackArrayLookup.v` and not this. The conflict is in the final
   handoff's frontier. *)
Require Export ZesuSsz.Automation.SpecTable.

(* C2: a word array satisfies a wanted byte array. *)
Require Export ZesuSsz.Automation.WordArrayBytes.

(* C2: the word a block loads lives inside an array the block holds. *)
Require Export ZesuSsz.Automation.StackArrayLookup.
