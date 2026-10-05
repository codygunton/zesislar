(* Enable only the loaded-word trace inclusion step in v2. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.LoadedTrace.

#[export] Instance zesu_switch_loaded_trace_set : ZesuRuleSetV2 := I.
#[export] Instance zesu_switch_loaded_trace : ZesuStepLoadedTrace := I.
