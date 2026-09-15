Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces
  WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactValueSpec
  WriteSuccessPostTransactionResources WriteSuccessOutputDescriptors
  WriteSuccessValueBlock.
Open Scope Z_scope.

Definition exactTailRawLoadOtherShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
    drop 1 writeSuccessTransactionsOtherRegisters.

Definition exactTailRawLoadEntry `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (transactionCount : nat)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat transactionCount)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat transactionCount)) ∗
   writeSuccessExactValueMemory sp values ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailRawLoadEntry) := I.

Definition exactTailRawLoadExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col exactTailRawLoadOtherShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessValueWord values 9) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessValueWord values 10) ∗
   writeSuccessExactValueMemory sp values ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailRawLoadExit) := I.
