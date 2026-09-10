Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15090.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15094.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadPrepare.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadReturn.

Lemma write_success_15090_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

Lemma write_success_transactions_chunk_15090_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15094 (writeSuccessTransactionsAt15094Spec P) -∗
  instr_body 0x15090 (writeSuccessTransactionsAt15090Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15090Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x15090 with "[]") as "#Hinstr15090".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15090.
    done. }
  iPoseProof (write_success_transactions_chunk_15090_load_prepare P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "[-Hnext]") as "Hstate".
  { rewrite /writeSuccessTransactionsAt15090Block.
    iFrame.
    iPureIntro.
    repeat split; try assumption.
    apply write_success_15090_current_unsigned; lia. }
  iAssert (instr_body 0x15094
    (writeSuccessTransactions15090LoadResult P sp base transaction
      transactions processed remaining bytes prefix suffix tail))%I
    with "[Hnext]" as "Hresult".
  { rewrite instr_pre'_eq. iIntros "Hresult".
    iApply "Hnext".
    iApply (write_success_transactions_chunk_15090_load_return P sp base
      transaction transactions processed remaining bytes prefix suffix tail
      with "Hresult"). }
  iPoseProof (write_success_transactions_chunk_15090_load_core P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hinstr15090 Hresult") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". iExact "Hstate".
Qed.
