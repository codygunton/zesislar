Require Import ZesuSsz.Automation.PureFacts.
Require Export ZesuSsz.Automation.InstrPreAddress.

#[export] Instance zesu_switch_instr_pre_address_set : ZesuRuleSetV2 := I.
#[export] Instance zesu_switch_instr_pre_address : ZesuStepInstrPreAddress := I.
