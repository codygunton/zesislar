Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15100.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15104.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Opaque WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.

Definition writeSuccessTransactionsAt15104Block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  writeSuccessTransactionPhaseHandoff TransactionNonce
    (writeSuccessTransactionsMachine15104
      sp base transactions processed transaction)
    sp base transaction transactions processed remaining
    bytes prefix suffix tail P.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15104Block) := I.

Lemma write_success_transactions_chunk_15100_auipc_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15104 (writeSuccessTransactionsAt15104Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail) -∗
  instr_body 0x15100 (writeSuccessTransactionsAt15100Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
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
  Unshelve.
  all: repeat iIntros "?".
  all: iRename select (writeSuccessTransactionOwn transaction) into
    "HtransactionOwn".
  all: iDestruct select (_ ∗ _)%I as
    "(Hremaining & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  all: liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
