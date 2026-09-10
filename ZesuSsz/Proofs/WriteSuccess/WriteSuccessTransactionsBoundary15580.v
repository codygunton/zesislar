From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15564.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15584.

Definition writeSuccessTransactions15580Frame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (pointer : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactions15584OtherRegShapes ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   writeSuccessTransactionsScratch15564Frame
     sp base transactions processed transaction ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 224) +
      32 * Z.of_nat
        (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Definition writeSuccessTransactionsAt15580Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (pointer : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x1557c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
    ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionAuthorizationCount
        sp transaction (writeSuccessTransactionsEvents sp remaining tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    writeSuccessTransactions15580Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail pointer P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15580Spec) := I.
