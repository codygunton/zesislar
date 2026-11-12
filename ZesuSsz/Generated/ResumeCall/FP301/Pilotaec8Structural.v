(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Export ZesuSsz.Compliance.ResumeCallHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaec8Entries.
#[export] Instance fp_machineAtaec8_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAtaec8_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAtaec8_ForwardA0N0.
#[export] Instance fp_machineAtaec8_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAtaec8_ForwardA0N0 (args) (returnAddress))
  (∃ (x5 : bv 64) (x6 : bv 64) (x7 : bv 64) (x15 : bv 64) (x16 : bv 64) (x17 : bv 64) (x28 : bv 64) (x29 : bv 64) (x30 : bv 64) (x31 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_input_end : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col (zesu_sys_regs) ∗ "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallReturnAddress args))) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallStackPointer args))) : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((resumeCallSavedFramePointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallInterpreterPointer args))) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallCallResultPointer args))) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallReturnOffset args))) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (resumeCallReturnSize args))) : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits ((resumeCallNewAccountStateGas args) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (x7 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (x28 : bv 64%N)) ∗ "x29" ↦ᵣ (RVal_Bits (x29 : bv 64%N)) ∗ "x30" ↦ᵣ (RVal_Bits (x30 : bv 64%N)) ∗ "x31" ↦ᵣ (RVal_Bits (x31 : bv 64%N)) ∗ (resumeCallInterpreterPointer args) ↦ₘ∗ (resumeCallBeforeInterpreter args) ∗ (resumeCallCallResultPointer args) ↦ₘ∗ (resumeCallCallResultBytes args) ∗ (resumeCallReturnDataPointer args) ↦ₘ∗ (resumeCallReturnDataBytes args) ∗ (resumeCallMemoryPointer args) ↦ₘ∗ (resumeCallBeforeMemory args) ∗ (resumeCallStackDataPointer args) ↦ₘ∗ (resumeCallBeforeStackData args) ∗ (((resumeCallStackPointer args - resumeCallStackBytes))%Z) ↦ₘ? (resumeCallStackBytes) ∗ ⌜(resumeCallDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (Z_to_bv 64 (resumeCallReturnAddress args)) mod 4 = 0)%Z)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAtaec8_unfold : LithiumUnfold (@fp_machineAtaec8) := I.
#[export] Typeclasses Opaque fp_machineAtaec8.
#[export] Instance fp_machineAtaec8_intro `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAtaec8 (args) (returnAddress) (K))
  (fp_machineAtaec8_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

