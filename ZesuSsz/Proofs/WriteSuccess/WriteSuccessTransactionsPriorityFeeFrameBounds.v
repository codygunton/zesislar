Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.

Lemma write_success_transactions_priority_fee_frame_bounds
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsPriorityFeeFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsPriorityFeeFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
  ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝.
Proof.
  iIntros "Hframe".
  iEval (unfold writeSuccessTransactionsPriorityFeeFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP & Hinv &
      Hexit & _)".
  iDestruct "Hinv" as "#Hinv".
  iPoseProof "Hinv" as "#HinvCopy".
  iEval (unfold writeSuccessTransactionsInvariant) in "HinvCopy".
  do 9 (iDestruct "HinvCopy" as "[_ HinvCopy]").
  iDestruct "HinvCopy" as "[%Halign HinvCopy]".
  iDestruct "HinvCopy" as "[%Hlower HinvCopy]".
  iDestruct "HinvCopy" as "[%Hupper _]".
  iAssert (writeSuccessTransactionsPriorityFeeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit]"
    as "Hframe".
  { rewrite /writeSuccessTransactionsPriorityFeeFrame.
    iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit".
  }
  iFrame "Hframe".
  iPureIntro. split; [exact Halign |].
  split; lia.
Qed.
