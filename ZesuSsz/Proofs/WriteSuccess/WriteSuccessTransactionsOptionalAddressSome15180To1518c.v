Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.

Lemma write_success_transactions_optional_address_some_15180_to_1518c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1518c (writeSuccessTransactionsOptionalAddressSomeAt1518cSpec P) -∗
  instr_body 0x15180 (writeSuccessTransactionsOptionalAddressSomeAt15180Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve; try lia.
  Unshelve.
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    base, tt)ₗ.
  iFrame.
  all: iAssumption.
Qed.
