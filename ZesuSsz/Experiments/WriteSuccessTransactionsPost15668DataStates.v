From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPost1566cDataSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (count : nat) (first second : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactionsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second pointer
      (Z_to_bv 64 (Z.of_nat count)) items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Definition writeSuccessTransactionsPost15670DataSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (count : nat) (first second ra : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second pointer
      (Z_to_bv 64 (Z.of_nat count)) items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Definition writeSuccessTransactionsPost15674DataSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (count : nat) (first second : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second pointer
      (Z_to_bv 64 (Z.of_nat count)) items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsPost1566cDataSpec) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactionsPost15670DataSpec) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactionsPost15674DataSpec) := I.
