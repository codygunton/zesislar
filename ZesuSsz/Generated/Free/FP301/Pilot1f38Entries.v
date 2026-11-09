(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Definition fp_machineAt1f38_ForwardA0N0 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) : iProp Sigma := (∃ (x10 : bv 64) (x14 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_input_end : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col (zesu_sys_regs) ∗ "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (freeReturnAddress args))) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (freeStackPointer args))) : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((freeSavedFramePointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits (x10 : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (freeBufferPointer args))) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (freeBufferLength args))) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (freeLog2Alignment args))) : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (x14 : bv 64%N)) ∗ (freeBufferPointer args) ↦ₘ∗ (freeBeforeBuffer args) ∗ (freeListsPointer) ↦ₘ∗ (freeBeforeLists args) ∗ (((freeStackPointer args - freeStackBytes))%Z) ↦ₘ? (freeStackBytes) ∗ ⌜(freeDomainAt returnAddress args)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I.

Definition fp_machineAt1f38 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma := (fp_machineAt1f38_ForwardA0N0 (args) (returnAddress) ∗ K)%I.
