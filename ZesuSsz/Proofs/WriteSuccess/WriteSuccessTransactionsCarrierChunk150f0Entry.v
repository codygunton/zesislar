Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactions150ecCarrierCallFrame.

Definition writeSuccessTransactionsMachine150f8CarrierCall
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     (["x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++ tmp_registers)) ∗
   reg_col [(KindReg "x11", BitsShape 64)] ∗
   reg_col (zip_with (fun register value =>
     (KindReg register, ExactShape value))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions150ecSavedValues transaction)) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x160f4) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 0x680)%bv ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsMachine150f8CarrierCall) := I.

Definition writeSuccessTransactionsAt150f0CarrierEntryBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine150f0CarrierCall
      sp base transactions processed transaction first second third fourth items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
       (writeSuccessTransactionsEvents sp remaining
         (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗
   writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗ True)%I.

Definition writeSuccessTransactionsAt150f8CarrierCallBlockFixed
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine150f8CarrierCall sp transaction ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
       (writeSuccessTransactionsEvents sp remaining
         (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗
   writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗ True)%I.

Definition writeSuccessTransactionsAt150f8CarrierCallSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsAt150f8CarrierCallBlockFixed P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f0CarrierEntryBlock) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f8CarrierCallBlockFixed) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f8CarrierCallSpec) := I.

Lemma write_success_transactions_carrier_chunk_150f0_entry_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150f8
    (writeSuccessTransactionsAt150f8CarrierCallBlockFixed P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items) -∗
  instr_body 0x150f0
    (writeSuccessTransactionsAt150f0CarrierEntryBlock P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
Qed.

Lemma write_success_transactions_carrier_chunk_150f0_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8CarrierCallSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0CarrierCallSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150f0CarrierCallSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail first second third fourth items) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iAssert (instr_body 0x150f8
      (writeSuccessTransactionsAt150f8CarrierCallBlockFixed P sp base transaction
        transactions processed remaining bytes prefix suffix tail
        first second third fourth items)) with "[Hnext]" as "HblockNext".
  { iApply (instr_pre_wand 0x150f8 0x150f8 false false with "Hnext");
      [done | done |].
    iIntros "Hblock".
    rewrite /writeSuccessTransactionsAt150f8CarrierCallSpec.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail, first, second, third, fourth, items.
    iExact "Hblock". }
  iPoseProof (write_success_transactions_carrier_chunk_150f0_entry_block P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode HblockNext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt150f0CarrierEntryBlock.
  iExact "Hentry".
Qed.
