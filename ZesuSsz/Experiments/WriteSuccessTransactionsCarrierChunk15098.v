From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15098.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState1509c.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions15098CarrierPhase
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

Global Instance writeSuccessTransactions15098CarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions15098CarrierPhase) := I.
Local Remove Hints writeSuccessTransactions15098CarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions15098CarrierPhase.

Definition writeSuccessTransactionsAt15098CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64)
    (items : list WriteSuccessByteLists.ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine15098Carrier
      sp base transactions processed transaction
      first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions15098CarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
   writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt15098CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_15098_raw
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
  instr_body 0x1509c (writeSuccessTransactionsAt1509cCarrierSpec P) -∗
  instr_body 0x15098 (writeSuccessTransactionsAt15098CarrierBlock P sp base
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
  all: rewrite /writeSuccessTransactionsMachine1509cCarrier /reg_col
    /writeSuccessTransactions1509cCarrierScratch
    /writeSuccessTransactions15098CarrierPhase.
  all: cbn.
  all: iFrame.
  all: try done.
  all: replace (bv_unsigned sp + 1640 + 8)%Z with
    (bv_unsigned sp + 1648)%Z by lia.
  all: iFrame.
  all: try done.
Qed.
Lemma write_success_transactions_carrier_chunk_15098
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1509c (writeSuccessTransactionsAt1509cCarrierSpec P) -∗
  instr_body 0x15098 (writeSuccessTransactionsAt15098CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15098CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15098_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt15098CarrierBlock
    /writeSuccessTransactions15098CarrierPhase.
  iExact "Hentry".
Qed.
