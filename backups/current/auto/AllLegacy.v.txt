Require Export InstrSpecs.Lookup.
Require Export InstrSpecs.Machine.
Require Export InstrSpecs.Specs.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Export ZesuSsz.Automation.Calls.
Require Export ZesuSsz.Automation.InstrPre.
Require Export ZesuSsz.Automation.Finish.
Require Import ZesuSsz.Automation.Rewrites.
Require Export ZesuSsz.Automation.Hooks.
Require Export ZesuSsz.Automation.UninitRegions.
Require Export ZesuSsz.Automation.NatBitvectors.
Require Export ZesuSsz.Automation.ArrayPacking.

#[export] Remove Hints subsume_instr_pre_zesu_inst
  subsume_instr_some_pre_inst : typeclass_instances.

#[export] Remove Hints zesu_bv_sign_extend_64_idemp
  bv_sign_extend_idemp zesu_bv_unsigned_Z_to_bv_small
  : isla_coq_rewrite lithium_rewrite.
#[export] Remove Hints Z_to_bv_add Z_to_bv_unsigned : lithium_rewrite.
#[export] Remove Hints zesu_integer_array_byte_equality : core.
#[export] Remove Hints zesu_integer_array_word_inhabited
  : typeclass_instances.

Ltac zesu_liAStep :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac liAStep ::= zesu_liAStep.
Ltac zesu_block ::= zesu_block_simpl.
