From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsProvider.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsWithdrawalsTotalTailFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp pointer : bv 64)
    (base : Z) (count : nat) (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsWithdrawalsPreservedRegisters) ∗
   "x1" ↦ᵣ: (fun _ => True) ∗
   "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ: (fun _ => True) ∗
   "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
   "x18" ↦ᵣ: (fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1120) ↦ₘ pointer ∗
   (bv_unsigned sp + 1128) ↦ₘ Z_to_bv 64 (Z.of_nat count) ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessWithdrawalsEvents sp count tail)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   writeSuccessTransactionsWithdrawalsTotalResources P sp pointer base count
     bytes tail ∗ True)%I.

Definition writeSuccessTransactionsWithdrawalsTotalAt15678Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (count : nat)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ: (fun _ => True) ∗ "x9" ↦ᵣ: (fun _ => True) ∗
    writeSuccessTransactionsWithdrawalsTotalTailFrame P sp pointer base count
      bytes tail)%I.

Definition writeSuccessTransactionsWithdrawalsTotalAt15680Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (count : nat)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat count)) ∗
    writeSuccessTransactionsWithdrawalsTotalTailFrame P sp pointer base count
      bytes tail)%I.

Definition writeSuccessTransactionsWithdrawalsTotalAt1568cRest
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp pointer : bv 64)
    (base : Z) (count : nat) (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col writeSuccessWithdrawalsOtherRegShapes ∗
   "x8" ↦ᵣ RVal_Bits pointer ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat count)) ∗
   writeSuccessWithdrawalsScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessWithdrawalsEvents sp count tail) ∗
   writeSuccessTransactionsWithdrawalsTotalResources P sp pointer base count
     bytes tail ∗ True)%I.

Definition writeSuccessTransactionsWithdrawalsTotalAt1568cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (count : nat)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x18" ↦ᵣ: (fun _ => True) ∗
    writeSuccessTransactionsWithdrawalsTotalAt1568cRest P sp pointer base count
      bytes tail)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalTailFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalAt15678Spec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalAt15680Spec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalAt1568cRest) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalAt1568cSpec) := I.
