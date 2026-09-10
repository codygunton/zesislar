From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

(** The state after [li x10, 1] at [0x15174]. *)
Definition writeSuccessTransactionsMachine15178 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15168OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15154) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 273) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_sign_extend 64
       (bv_extract 0 32
         (bv_or
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284))
               (BV 64 24))
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283))
               (BV 64 16)))
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282))
               (BV 64 8))
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 281)))))) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗
   writeSuccessTransactionsScratch15174
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15178) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15178Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 285 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionTo
      (writeSuccessTransactionsMachine15178 sp base transactions processed transaction)
      sp base transaction transactions processed remaining bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsOptionalAddressSomeAt15178Spec) := I.
