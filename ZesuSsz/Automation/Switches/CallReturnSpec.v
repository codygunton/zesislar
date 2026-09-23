(* Enable the table-backed call-return step alone for a benchmark arm. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.CallReturnSpec.
Require Import ZesuSsz.Automation.SpecTable.
Require Import isla.riscv64.riscv64.

Global Instance zesu_switch_call_return_spec_set : ZesuRuleSetV2 := I.
Global Instance zesu_switch_call_return_spec : ZesuStepCallReturnSpec := I.
Global Instance zesu_switch_call_return_spec_table
    `{!islaG Sigma} `{!threadG} pc body
    `{!ZesuSpecAt pc body} : ZesuReturnTableEntry pc body := I.
