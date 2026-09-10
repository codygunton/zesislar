Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.

Definition writeSuccessTransactionsCarrierOutputTail
    (sp : bv 64) (items : list ByteListItem) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (byteListItemEvents (sp - BV 64 32)%bv items
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail)).

Definition writeSuccessTransactions150ecCarrierCallFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col
      (delete 0%nat
        (delete 3%nat
          (delete 3%nat writeSuccessTransactions15028OtherRegShapes))) ∗
   writeSuccessTransactions150ecCarrierScratch
     sp base (length transactions) (length processed) transaction
     first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
     writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessByteArrayOwn (writeSuccessTransactionDataPointer transaction)
     (writeSuccessTransactionData transaction) ∗
   writeSuccessTransactionRestOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
       first second third fourth items) ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions150ecCarrierCallFrame.

Definition writeSuccessTransactions150ecCallerRegisters : list string :=
  ["x5"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions150ecCallerValues
    (transaction : writeSuccessTransaction) : list valu :=
  [RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
         (BV 64 16)));
   RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
         (BV 64 8))
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 277)));
   RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 268))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 267))
         (BV 64 16)));
   RVal_Bits (writeSuccessTransactionWord transaction 248);
   RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_or
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 280))
               (BV 64 24))
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 279))
               (BV 64 16)))
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
               (BV 64 8))
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 277))))
         (BV 64 32))
       (bv_or
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276))
             (BV 64 24))
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
             (BV 64 16)))
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 274))
             (BV 64 8))
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 273)))));
   RVal_Bits
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
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281))));
   RVal_Bits (writeSuccessTransactionWord transaction 128);
   RVal_Bits (writeSuccessTransactions15078Upper transaction);
   RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
         (BV 64 16)));
   RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 270))
         (BV 64 8))
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 269)));
   RVal_Bits (writeSuccessTransactionWord transaction 64);
   RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
       (BV 64 16));
   RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
       (BV 64 8))].

Definition writeSuccessTransactions150ecSavedValues
    (transaction : writeSuccessTransaction) : list valu :=
  [RVal_Bits (writeSuccessTransactionWord transaction 192);
   RVal_Bits (writeSuccessTransactionWord transaction 16);
   RVal_Bits (writeSuccessTransactionWord transaction 48);
   RVal_Bits (writeSuccessTransactionWord transaction 224);
   RVal_Bits (writeSuccessTransactionWord transaction 56);
   RVal_Bits (writeSuccessTransactionWord transaction 72);
   RVal_Bits (writeSuccessTransactionWord transaction 200);
   RVal_Bits (writeSuccessTransactionWord transaction 24);
   RVal_Bits (writeSuccessTransactionWord transaction 8);
   RVal_Bits (writeSuccessTransactionWord transaction 0);
   RVal_Bits (writeSuccessTransactionWord transaction 184);
   RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))].

Definition writeSuccessTransactionsAt10190CarrierCallSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
      writeSuccessTransactions150ecCallerRegisters
      (writeSuccessTransactions150ecCallerValues transaction)) ∗
    reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
      ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
       "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
      (writeSuccessTransactions150ecSavedValues transaction)) ∗
    "x10" ↦ᵣ RVal_Bits (bv_add sp (BV 64 1744)) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
          (writeSuccessTransactionsEvents sp remaining
            (writeSuccessTransactionsCarrierOutputTail sp items tail)))) ∗
    writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt10190CarrierCallSpec) := I.

Definition writeSuccessTransactionsMachine150f0CarrierCall
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     (["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++
       tmp_registers)) ∗
   reg_col [(KindReg "x10", BitsShape 64);
     (KindReg "x11", BitsShape 64)] ∗
   reg_col (zip_with (fun register value =>
     (KindReg register, ExactShape value))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions150ecSavedValues transaction)) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsMachine150f0CarrierCall) := I.

Definition writeSuccessTransactionsAt150f0CarrierCallSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsMachine150f0CarrierCall
      sp base transactions processed transaction
      first second third fourth items ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining
          (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗
    writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f0CarrierCallSpec) := I.
