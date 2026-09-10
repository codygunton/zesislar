Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151a8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadPrepare.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadReturn.

Lemma write_success_transactions_chunk_151a4_to_151a8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151a8 (writeSuccessTransactionsAt151a8Spec P) -∗
  instr_body 0x151a4 (writeSuccessTransactionsAt151a4Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt151a4Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "Hblock".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x151a4 with "[]") as "#Hinstr151a4".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a151a4.
    done. }
  iPoseProof (write_success_transactions_151a4_load_prepare P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hblock") as "Hstate".
  iAssert (instr_body 0x151a8
    (writeSuccessTransactions151a4LoadResult P sp base transaction
      transactions processed remaining bytes prefix suffix tail))%I
    with "[Hnext]" as "Hresult".
  { rewrite instr_pre'_eq. iIntros "Hresult".
    iApply "Hnext".
    iApply (write_success_transactions_151a4_load_return P sp base transaction
      transactions processed remaining bytes prefix suffix tail with "Hresult"). }
  iPoseProof (write_success_transactions_151a4_load_core P sp base transaction
    transactions processed remaining bytes prefix suffix tail with
    "Hinstr151a4 Hresult") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". iExact "Hstate".
Qed.
