Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.

Lemma write_success_transactions_10190_frame_facts
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions150ecCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions150ecCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝.
Proof.
  iIntros "Hframe".
  iEval (unfold writeSuccessTransactions150ecCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  iDestruct "Hinvariant" as "#Hinvariant".
  iPoseProof "Hinvariant" as "Hfacts".
  iEval (unfold writeSuccessTransactionsInvariant) in "Hfacts".
  iDestruct "Hfacts" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %HspAlign & %HspMin &
      %HspMax & _)".
  iSplitL "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hexit".
  - rewrite /writeSuccessTransactions150ecCallFrame.
    iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP
      Hinvariant Hexit".
  - repeat iSplit; iPureIntro; try assumption; lia.
Qed.
