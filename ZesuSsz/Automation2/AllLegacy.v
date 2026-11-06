Require Export InstrSpecs.Lookup.
Require Export InstrSpecs.Machine.
Require Export InstrSpecs.Specs.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Export ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Automation2.InstrPre.
Require Export ZesuSsz.Automation2.Legacy.Finish.
Require Import ZesuSsz.Automation2.Rewrites.
Require Export ZesuSsz.Automation2.Legacy.Hooks.
Require Export ZesuSsz.Automation2.UninitRegions.
Require Export ZesuSsz.Automation2.NatBitvectors.
Require Export ZesuSsz.Automation2.ArrayPacking.

#[export] Remove Hints subsume_instr_pre_zesu_inst
  subsume_instr_some_pre_inst : typeclass_instances.

#[export] Remove Hints zesu_bv_sign_extend_64_idemp
  bv_sign_extend_idemp zesu_bv_unsigned_Z_to_bv_small
  : isla_coq_rewrite lithium_rewrite.
#[export] Remove Hints Z_to_bv_add Z_to_bv_unsigned : lithium_rewrite.
#[export] Remove Hints zesu_integer_array_byte_equality : core.
#[export] Remove Hints zesu_integer_array_word_inhabited
  : typeclass_instances.
