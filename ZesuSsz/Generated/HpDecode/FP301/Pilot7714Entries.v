(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.HpDecodeContract.
Require Export ZesuSsz.Compliance.HpDecodeHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Definition fp_machineAt7714_ForwardA0N0 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) : iProp Sigma := (∃ (x15 : bv 64) (x16 : bv 64) (x17 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_input_end : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col (zesu_sys_regs) ∗ "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeReturnAddress args))) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeStackPointer args))) : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((hpDecodeSavedFramePointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeResultPointer args))) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeInputPointer args))) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeInputLength args))) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeOutputPointer args))) : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (hpDecodeOutputLength args))) : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ (hpDecodeInputPointer args) ↦ₘ∗ (hpDecodeInputBytes args) ∗ (hpDecodeOutputPointer args) ↦ₘ∗ (hpDecodeBeforeOutput args) ∗ (hpDecodeResultPointer args) ↦ₘ∗ (hpDecodeBeforeResult args) ∗ (((hpDecodeStackPointer args - hpDecodeStackBytes))%Z) ↦ₘ? (hpDecodeStackBytes) ∗ ⌜(hpDecodeDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (Z_to_bv 64 (hpDecodeReturnAddress args)) mod 4 = 0)%Z)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I.

Definition fp_machineAt7714 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma := (fp_machineAt7714_ForwardA0N0 (args) (returnAddress) ∗ K)%I.
