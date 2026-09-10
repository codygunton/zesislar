From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.

Import ListNotations.

Definition writeSuccessTransactions15640Frame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (P : iProp Sigma) :
    iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"]) ∗
   writeSuccessTransactionsScratch15620Tail
     sp base transactions processed transaction ∗
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

Definition writeSuccessTransactionsAt15640Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (pointer : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      tmp_registers) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x1563c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 96) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 104) ∗
    "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 112) ∗
    "x13" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 120) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x14"; "x15"; "x16"; "x17"]) ∗
    "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionR sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    ⌜bv_unsigned pointer =
      (bv_unsigned (writeSuccessTransactionWord transaction 240) +
       144 * Z.of_nat
         (length (writeSuccessTransactionAuthorizations transaction)))%Z⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    writeSuccessTransactions15640Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15640Spec) := I.
