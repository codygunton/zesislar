Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Definition writeSuccessTransactionsMachine151a8 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col
     ((fun register => (KindReg register, BitsShape 64)) <$>
        ["x1"; "x3"; "x4"; "x6"; "x7";
         "x13"; "x14"; "x15"; "x16"; "x17";
         "x28"; "x29"; "x30"; "x31"]) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   ("x5" ↦ᵣ: fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x11" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x12" ↦ᵣ RVal_Bits (bv_sign_extend 64
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)) ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) ∗
   writeSuccessTransactionsScratch1519c
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine151a8) := I.

Definition writeSuccessTransactionsAt151a8Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned (sp + 128)⌝ ∗
    ⌜bv_unsigned (sp + 128) <= machineRamEnd defaultMap - 8⌝ ∗
    WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
      WriteSuccessTransactionsSpec.TransactionValue
      (writeSuccessTransactionsMachine151a8
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt151a8Spec) := I.
