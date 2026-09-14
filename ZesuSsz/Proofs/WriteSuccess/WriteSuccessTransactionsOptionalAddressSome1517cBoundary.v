Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15178Handoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessTransactionsOptionalAddressSomeFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
   ⌜writeSuccessTransactionTo transaction <> None⌝ ∗
   True)%I.

Global Typeclasses Opaque writeSuccessTransactionsOptionalAddressSomeFrame.

Definition writeSuccessTransactionsOptionalAddressSomeCallerFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   ((bv_unsigned sp - 16) ↦ₘ? 16 -∗
     writeSuccessTransactionsScratch15174
       sp base transactions processed transaction) ∗
   writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactionsOptionalAddressSomeCallerFrame.

Definition writeSuccessTransactionsMachine15180
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) (r10 r11 : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15168OtherRegShapes ∗
   "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits r10 ∗ "x11" ↦ᵣ RVal_Bits r11 ∗
   "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15180) := I.

Definition writeSuccessTransactionsOptionalAddressSomeBooleanSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"]) ∗
    reg_col
      [(KindReg "x8", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 192)));
       (KindReg "x9", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 16)));
       (KindReg "x18", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 48)));
       (KindReg "x19", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 224)));
       (KindReg "x20", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 56)));
       (KindReg "x21", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 72)));
       (KindReg "x22", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 200)));
       (KindReg "x23", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 24)));
       (KindReg "x24", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 8)));
       (KindReg "x25", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 0)));
       (KindReg "x26", ExactShape
          (RVal_Bits (writeSuccessTransactionWord transaction 184)));
       (KindReg "x27", ExactShape (RVal_Bits
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))))] ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x16178) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 273) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
      (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 20)
        (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
          (writeSuccessTransactionsEvents sp remaining tail)))) ∗
    writeSuccessTransactionsOptionalAddressSomeCallerFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSomeBooleanSetupSpec) := I.

Definition writeSuccessTransactionsOptionalAddressSomePostSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec) (r10 r11 : bv 64),
    writeSuccessTransactionsMachine15180
      sp base transactions processed transaction r10 r11 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 20)
      (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSomePostSpec) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15180Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessTransactionsOptionalAddressSomePostSpec P.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSomeAt15180Spec) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt1518cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactions15168OtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x10188) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
    "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
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
    "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
    writeSuccessTransactionsScratch15174
      sp base transactions processed transaction ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 20)
      (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSomeAt1518cSpec) := I.
