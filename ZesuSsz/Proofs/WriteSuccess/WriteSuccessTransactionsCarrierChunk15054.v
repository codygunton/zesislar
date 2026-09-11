Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15054.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15058.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions15054CarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64)
    (items : list WriteSuccessByteLists.ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions15054CarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions15054CarrierPhase) := I.
Local Remove Hints writeSuccessTransactions15054CarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions15054CarrierPhase.

Definition writeSuccessTransactionsAt15054CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64)
    (items : list WriteSuccessByteLists.ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine15054Carrier
      sp base transactions processed transaction
      first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions15054CarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
   writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt15054CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_15054_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64)
    (items : list WriteSuccessByteLists.ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058CarrierSpec P) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054CarrierBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  all: iExists (items, fourth, third, second, first, tail, suffix, prefix,
    bytes, remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  all: cbn.
  all: rewrite /writeSuccessTransactionsMachine15058Carrier /reg_col
    /writeSuccessTransactions15058CarrierScratch
    /writeSuccessTransactions15054CarrierPhase.
  all: cbn.
  all: iFrame.
  all: try done.
  all: replace (bv_unsigned sp + 144 + 8)%Z with
    (bv_unsigned sp + 152)%Z by lia.
  all: iFrame.
  all: try done.
Qed.

Lemma write_success_transactions_carrier_chunk_15054
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058CarrierSpec P) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15054CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15054_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt15054CarrierBlock
    /writeSuccessTransactions15054CarrierPhase.
  iExact "Hentry".
Qed.
