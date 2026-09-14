Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsWithdrawalsTailFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp pointer : bv 64)
    (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsWithdrawalsPreservedRegisters) ∗
   "x1" ↦ᵣ: (fun _ => True) ∗
   "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ: (fun _ => True) ∗
   "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
   "x18" ↦ᵣ: (fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1120) ↦ₘ pointer ∗
   (bv_unsigned sp + 1128) ↦ₘ
     Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessWithdrawalsEvents sp (S remaining) tail)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessTransactionsWithdrawalsResources P sp pointer base total
     processed remaining bytes prefix suffix tail ∗ True)%I.

Definition writeSuccessTransactionsWithdrawalsAt15678Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ: (fun _ => True) ∗ "x9" ↦ᵣ: (fun _ => True) ∗
    writeSuccessTransactionsWithdrawalsTailFrame P sp pointer base total
      processed remaining bytes prefix suffix tail)%I.

Definition writeSuccessTransactionsWithdrawalsAt15680Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    writeSuccessTransactionsWithdrawalsTailFrame P sp pointer base total
      processed remaining bytes prefix suffix tail)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTailFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsAt15678Spec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsAt15680Spec) := I.
