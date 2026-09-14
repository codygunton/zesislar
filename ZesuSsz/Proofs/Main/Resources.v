Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition mainFrameSp (sp : bv 64) : bv 64 := (sp - BV 64 896)%bv.

Definition mainPrologueEntry `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 saved size : bv 64) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) + 896 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits a0 ∗ "x11" ↦ᵣ RVal_Bits a1 ∗
   bv_unsigned (mainFrameSp sp + BV 64 888)%bv ↦ₘ saved ∗
   bv_unsigned (mainFrameSp sp + BV 64 8)%bv ↦ₘ size ∗ True)%I.

Definition mainReadInputCall `{!islaG Sigma} `{!threadG}
    (sp ra : bv 64) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) + 896 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
   "x2" ↦ᵣ RVal_Bits (mainFrameSp sp) ∗
   "x10" ↦ᵣ RVal_Bits (mainFrameSp sp) ∗
   "x11" ↦ᵣ RVal_Bits (mainFrameSp sp + BV 64 8)%bv ∗
   bv_unsigned (mainFrameSp sp + BV 64 888)%bv ↦ₘ ra ∗
   bv_unsigned (mainFrameSp sp + BV 64 8)%bv ↦ₘ (BV 64 0) ∗ True)%I.

Global Instance : LithiumUnfold (@mainPrologueEntry) := I.
Global Instance : LithiumUnfold (@mainReadInputCall) := I.

Definition mainCallRegisters `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits a0 ∗ "x11" ↦ᵣ RVal_Bits a1 ∗ True)%I.
Global Instance : LithiumUnfold (@mainCallRegisters) := I.

Definition mainDispatchMemory `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (status : bv 16) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 896 < (machineRamEnd defaultMap)⌝ ∗
   bv_unsigned (sp + BV 64 880)%bv ↦ₘ status ∗ True)%I.
Global Instance : LithiumUnfold (@mainDispatchMemory) := I.
