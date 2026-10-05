(* Enable only the owned-conjunct matcher in v2. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Export ZesuSsz.Automation.ConjunctMatch.

#[export] Instance zesu_switch_conjunct_match_set : ZesuRuleSetV2 := I.
#[export] Instance zesu_switch_conjunct_match : ZesuStepConjunctMatch := I.
