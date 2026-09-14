Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.

Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150ecCallSpec.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150ecJump.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame
  writeSuccessTransactions150ecCarrierScratch.

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
Print Assumptions write_success_transactions_carrier_chunk_150ec_jump.
