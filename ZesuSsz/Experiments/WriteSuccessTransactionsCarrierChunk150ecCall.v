From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame
  writeSuccessTransactions150ecCarrierScratch.

Definition writeSuccessTransactionsAt150ecCarrierCallBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     writeSuccessTransactions150ecCallerRegisters
     (writeSuccessTransactions150ecCallerValues transaction)) ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions150ecSavedValues transaction)) ∗
   "x10" ↦ᵣ RVal_Bits (bv_add sp (BV 64 1744)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x100e8) ∗
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

Definition writeSuccessTransactionsAt10190CarrierCallBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     writeSuccessTransactions150ecCallerRegisters
     (writeSuccessTransactions150ecCallerValues transaction)) ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
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
    (@writeSuccessTransactionsAt150ecCarrierCallBlock) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt10190CarrierCallBlock) := I.

Lemma write_success_transactions_carrier_chunk_150ec_jump_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190CarrierCallBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierCallBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
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
  all: try (unfold writeSuccessTransactionsCarrierOutputTail; iFrame).
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (unfold writeSuccessTransactionsCarrierOutputTail; iFrame).
  Unshelve. all: try exact inhabitant.
Qed.

Lemma write_success_transactions_carrier_chunk_150ec_jump
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190CarrierCallSpec P) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150ecCarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail first second third fourth items) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iAssert (instr_pre 0x10190
      (writeSuccessTransactionsAt10190CarrierCallBlock P sp base transaction
        transactions processed remaining bytes prefix suffix tail
        first second third fourth items)) with "[Hnext]" as "HblockNext".
  { iApply (instr_pre_wand 0x10190 0x10190 true true with "Hnext");
      [done | done |].
    iIntros "Hblock".
    rewrite /writeSuccessTransactionsAt10190CarrierCallSpec
      /writeSuccessTransactionsAt10190CarrierCallBlock.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail, first, second, third, fourth, items.
    iExact "Hblock". }
  iPoseProof (write_success_transactions_carrier_chunk_150ec_jump_block P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode HblockNext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hphase & HloadFacts & _)".
  iEval (unfold writeSuccessTransactionsMachine150ecCarrier) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 &
      H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 &
      H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hscratch & _)".
  iEval (unfold writeSuccessTransactionsCurrentPhaseCarrierFrame) in "Hphase".
  iDestruct "Hphase" as
    "(Hprefix & Hsuffix & Hprocessed & Hdata & Hrest & Hremaining & Hmmio &
      Htrace & HP & Hinvariant & Hexit & _)".
  rewrite /writeSuccessTransactionsAt150ecCarrierCallBlock
    /writeSuccessTransactions150ecCallerRegisters
    /writeSuccessTransactions150ecCallerValues
    /writeSuccessTransactions150ecSavedValues
    /writeSuccessTransactions150ecCarrierCallFrame
    !reg_col_cons reg_col_nil.
  cbn. iFrame.
  repeat iSplit; iPureIntro; done.
Qed.
