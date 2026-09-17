Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.

Definition transactionCarrierPostLbuArray `{!islaG Sigma}
    (address : Z) (values : list (bv 8)) (index : nat) : iProp Sigma :=
  (∃ byte : bv 8,
    address ↦ₘ∗ take index values ∗
    (address + Z.of_nat index) ↦ₘ byte ∗
    (address + Z.of_nat (S index)) ↦ₘ∗ drop (S index) values ∗
    ⌜values !! index = Some byte⌝)%I.

Lemma transaction_carrier_post_lbu_array_restore `{!islaG Sigma}
    address values index :
  transactionCarrierPostLbuArray address values index -∗
  address ↦ₘ∗ values.
Proof.
  iIntros "Hsplit".
  iDestruct "Hsplit" as (byte) "(Hprefix & Hbyte & Hsuffix & %Hlookup)".
  iApply (mem_mapsto_array_recombine_u8_read address values index byte
    (address + Z.of_nat (S index)) (address + Z.of_nat index)
    with "Hprefix Hsuffix Hbyte");
    iPureIntro; try exact Hlookup; reflexivity.
Qed.
Print Assumptions transaction_carrier_post_lbu_array_restore.

Definition writeSuccessTransactionsAt14fa8CarrierSplitSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsMachine14fa8Carrier sp base transactions processed
      transaction first second third fourth items ∗
    transactionCarrierPostLbuArray
      (base + 288 * Z.of_nat (length processed))
      (writeSuccessTransactionBytes transaction) 267 ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗ True)%I.

Lemma transaction_carrier_14fa8_split_restores_exact `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  writeSuccessTransactionsAt14fa8CarrierSplitSpec P -∗
  writeSuccessTransactionsAt14fa8CarrierSpec P.
Proof.
  iIntros "Hsplit".
  iDestruct "Hsplit" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail first second third fourth items)
    "(Hmachine & HarraySplit & Hframe & Hfacts & _)".
  iPoseProof (transaction_carrier_post_lbu_array_restore with "HarraySplit")
    as "Harray".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail, first, second, third, fourth, items.
  iFrame.
Qed.
Print Assumptions transaction_carrier_14fa8_split_restores_exact.
