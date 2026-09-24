(* Opt in to the T1 loaded-word rewrite without changing the v2 set. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.LoadedWordTrace.

Global Instance zesu_switch_loaded_word_set : ZesuRuleSetV2 := I.
Global Instance zesu_switch_loaded_word_trace : ZesuStepLoadedWordTrace := I.
