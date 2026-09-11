Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1501c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15018.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState1501c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15020.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15024.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15018.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk1501cRaw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15020Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15024Raw.

Lemma write_success_transactions_carrier_chunk_15024
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028CarrierSpec P) -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15024CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & Hbuild & Harray & Hphase &
      Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed.
  { apply write_success_1501c_current_unsigned; lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15024_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt15024CarrierBlock
    /writeSuccessTransactions15024CarrierPhase.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_transactions_carrier_chunk_15020
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024CarrierSpec P) -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15020CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & Hbuild & Harray & Hphase &
      Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed.
  { apply write_success_1501c_current_unsigned; lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15020_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt15020CarrierBlock
    /writeSuccessTransactions15020CarrierPhase.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_transactions_carrier_chunk_1501c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020CarrierSpec P) -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1501cCarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & Hbuild & Harray & Hphase &
      Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed.
  { apply write_success_1501c_current_unsigned; lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_1501c_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt1501cCarrierBlock
    /writeSuccessTransactions1501cCarrierPhase.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_transactions_carrier_chunk_15018_to_15028
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028CarrierSpec P) -∗
  instr_body 0x15018 (writeSuccessTransactionsAt15018CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15024 P with
    "Hlookup Hcode Hnext") as "H15024".
  iPoseProof (write_success_transactions_carrier_chunk_15020 P with
    "Hlookup Hcode H15024") as "H15020".
  iPoseProof (write_success_transactions_carrier_chunk_1501c P with
    "Hlookup Hcode H15020") as "H1501c".
  iApply (write_success_transactions_carrier_chunk_15018 P with
    "Hlookup Hcode H1501c").
Qed.
