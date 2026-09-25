(* One rule of rule set v2 and no other: the C9 return wand, whatever
   its conclusion. Not in `Switch.v` or `Sets/v2.v`: an arm imports this
   file to measure the rule. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ReturnWand.

Global Instance zesu_switch_return_wand_set : ZesuRuleSetV2 := I.
Global Instance zesu_switch_return_wand : ZesuStepReturnWand := I.
