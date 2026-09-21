(* Turn on the finisher's C6 step.

   `PureFacts.v` states the step and `Finish.v` calls it, guarded by a
   class with no instance. This file is the instance. Import it, or rule
   set v2, and a pure goal the finisher has refused gets one more try
   with the witness's facts unfolded.

   It is a separate file because the guard exists to keep rule set v1's
   outcomes identical, and a rule that turns itself on is not a guard. *)

Require Import ZesuSsz.Automation.PureFacts.

Global Instance zesu_witness_arith_on : ZesuWitnessArithEnabled := I.
