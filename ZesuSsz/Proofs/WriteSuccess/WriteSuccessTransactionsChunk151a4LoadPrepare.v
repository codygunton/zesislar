Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadState.

Lemma write_success_transactions_151a4_load_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt151a4Block P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions151a4LoadState P sp base transaction transactions
    processed remaining bytes prefix suffix tail.
Proof.
  rewrite /writeSuccessTransactionsAt151a4Block.
  iIntros "(%Halign & %Hmin & %Hmax & Hphase)".
  iDestruct "Hphase" as
    "(Hmachine & HbasePrefix & HbaseSuffix & Hprocessed & Htransaction &
      Hremaining & Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  iPoseProof "Hinvariant" as "#HinvCopy".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %HspAlign & %HspMin & %HspMax & _)".
  iPoseProof (write_success_transactions_151a4_load_machine_frame
    sp base transactions processed transaction
    with "Hmachine") as "(Hsys & H12 & H2 & Hword & Hframe)".
  rewrite /writeSuccessTransactions151a4LoadState.
  iFrame "Hsys H12 H2 Hword Hframe".
  rewrite /writeSuccessTransactions151a4Outer
    /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iFrame "HbasePrefix HbaseSuffix Hprocessed Htransaction Hremaining Hmmio
    Htrace HP Hinvariant Hexit".
  repeat iSplit; first by iPureIntro.
  all: try done.
Qed.
