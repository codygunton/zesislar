Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.

Import ListNotations.

Definition writeSuccessTransactions15658Frame `{!islaG Sigma} `{!threadG}
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
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
   True)%I.

Definition writeSuccessTransactionsAt15658Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (pointer : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      tmp_registers) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15654) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 128) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 136) ∗
    "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 144) ∗
    "x13" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 152) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x14"; "x15"; "x16"; "x17"]) ∗
    "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionS sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    ⌜bv_unsigned pointer =
      (bv_unsigned (writeSuccessTransactionWord transaction 240) +
       144 * Z.of_nat
         (length (writeSuccessTransactionAuthorizations transaction)))%Z⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessTransactions15658Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15658Spec) := I.
