(* Enable only the returning-call continuation into a load spec. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.CallReturnSpecTable.

#[export] Instance zesu_switch_call_return_spec_table_set : ZesuRuleSetV2 := I.
#[export] Instance zesu_switch_call_return_spec_table :
  ZesuStepCallReturnSpecTable := I.
