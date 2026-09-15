Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces
 WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessTransactionsSpec
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactValueSpec WriteSuccessOutputDescriptors
 WriteSuccessValueBlock.
Open Scope Z_scope.
Definition exactTailRawReadyOtherShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
    drop 1 writeSuccessTransactionsOtherRegisters.
Definition exactTailRawReady `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col zesu_ram_sys_regs ∗ reg_col exactTailRawReadyOtherShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessValueWord values 9) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessValueWord values 10) ∗
    writeSuccessTransactionBase witness ↦ₘ∗
      WriteSuccessNativeContract.writeSuccessTransactionBytes witness ∗
    writeSuccessTransactionsOwn (writeSuccessTransactions witness) ∗
    transactionLiveScratch sp (writeSuccessTransactionBase witness)
      (length (writeSuccessTransactions witness)) ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessExactTailEvents witness) ∗
    writeSuccessExactTailCallerWithCopiedWords args witness ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailRawReady) := I.
