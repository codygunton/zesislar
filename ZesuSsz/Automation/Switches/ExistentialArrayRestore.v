Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ExistentialArrayRestore.

#[export] Instance zesu_switch_existential_array_restore_set : ZesuRuleSetV2 := I.
#[export] Instance zesu_switch_existential_array_restore :
  ZesuStepExistentialArrayRestore := I.
