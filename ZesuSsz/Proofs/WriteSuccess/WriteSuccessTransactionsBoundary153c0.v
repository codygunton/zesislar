Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Import ListNotations.

Definition writeSuccessTransactions153c0OtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions153c0OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions153c0OtherRegisters.

Definition writeSuccessTransactionsScratch153c0 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ? 8 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1616 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch153c0) := I.

Definition writeSuccessTransactionsMachine153c0 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions153c0OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64
       (Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)))) ∗
   "x11" ↦ᵣ RVal_Bits
     (Z_to_bv 64
       (Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)))) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessTransactionsScratch153c0
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine153c0) := I.

Definition writeSuccessTransactionsAt153c0Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionBlobCount
      (writeSuccessTransactionsMachine153c0
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt153c0Spec) := I.
