From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1501c.
Require Import ZesuSsz.Experiments.WriteSuccessInstrBodyAdapters.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fc8To14fe0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fe0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fe4.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fe8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14ff0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15018.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Definition writeSuccessTransactionsAt14fc8Prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine14fc8
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14fc8Prefix) := I.

Lemma write_success_14fc8_transaction_byte_lookup
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (index : nat) :
  (index < length
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction))%nat ->
  WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction !! index =
    Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction index).
Proof.
  intros Hindex.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
    transaction !! index) eqn:Hlookup; [done |].
  apply lookup_ge_None_1 in Hlookup. lia.
Qed.

Lemma write_success_transactions_chunk_14fc8_prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cSpec P) -∗
  instr_body 0x14fc8 (writeSuccessTransactionsAt14fc8Prefix P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_chunk_15018 P with
    "Hlookup Hcode Hnext") as "H15018".
  iPoseProof (write_success_transactions_chunk_14ff0 P with
    "Hlookup Hcode H15018") as "H14ff0".
  iPoseProof (write_success_transactions_chunk_14fec P with
    "Hlookup Hcode H14ff0") as "H14fec".
  iPoseProof (write_success_transactions_chunk_14fe8 P with
    "Hlookup Hcode H14fec") as "H14fe8".
  iPoseProof (write_success_transactions_chunk_14fe4 P with
    "Hlookup Hcode H14fe8") as "H14fe4".
  iPoseProof (write_success_transactions_chunk_14fe0 P with
    "Hlookup Hcode H14fe4") as "H14fe0".
  iPoseProof (write_success_transactions_chunk_14fc8_to_14fe0 P with
    "Hlookup Hcode H14fe0") as "H14fc8".
  iApply (instr_body_wand_adapter 0x14fc8
    (writeSuccessTransactionsAt14fc8Spec P)
    (writeSuccessTransactionsAt14fc8Prefix P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    with "[] H14fc8").
  rewrite /writeSuccessTransactionsAt14fc8Spec
    /writeSuccessTransactionsAt14fc8Prefix.
  iIntros "Hentry".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iExact "Hentry".
Qed.
