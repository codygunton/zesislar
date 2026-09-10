From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1562c.

Definition writeSuccessTransactions15628OtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16";
   "x17"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions15628OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions15628OtherRegisters.

Definition writeSuccessTransactions15628Frame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ pointer : bv 64,
   reg_col writeSuccessTransactions15628OtherRegShapes ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 240) +
      144 * Z.of_nat
        (length (writeSuccessTransactionAuthorizations transaction)))%Z⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗
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

Definition writeSuccessTransactionsAt15628Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15624) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 256) ∗
    ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionV sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    writeSuccessTransactions15628Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15628Spec) := I.
