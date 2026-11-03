Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.UnionRuleComponents.

(* The v3.5 dispatcher can call this helper after its new branches.
   This module installs no dispatcher and preserves all 34 captured branches. *)
Ltac zesu_original_dispatcher184 :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    ZesuSsz.Automation.UnionRuleComponents.zesu_region_fault_if_enabled
  | zesu_expose_instruction_lookup
  | zesu_region_fault_if_enabled
  | zesu_ram_fault_if_enabled
  | zesu_signed_address_if_enabled
  | zesu_stack_write_if_enabled
  | zesu_handoff_goal_address_if_enabled
  | zesu_handoff_memory_if_enabled
  | zesu_handoff_adjacent_words_if_enabled
  | zesu_handoff_facts_if_enabled
  | zesu_handoff_integer_equality_if_enabled
  | zesu_integer_array_address_if_enabled
  | zesu_normalize_find_mem_address
  | ZesuSsz.Automation.UnionRuleComponents.block2_f6_select_generic_write
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | zesu_pure_fact_hints_if_enabled
  | zesu_known_pair_conjunct_witness_if_enabled
  | liUnfoldEarly
  | zesu_conjunct_head_if_enabled
  | zesu_known_pair_witness_if_enabled
  | zesu_pure_witness_constraints_if_enabled
  | zesu_record_witness_if_enabled
  | zesu_primitive_tuple_if_enabled
  | zesu_liInstrPreMatch
  | zesu_preserve_current_unsigned
  | zesu_register_collection_selection_if_enabled
  | liStep
  | liLetBindHint
  | liUnfoldLate
  | zesu_canonical_fact_views_if_enabled
 ]; liSimpl.
