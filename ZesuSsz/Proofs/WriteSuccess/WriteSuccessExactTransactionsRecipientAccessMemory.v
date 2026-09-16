Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientValueRegion
  WriteSuccessExactTransactionsRecipientOutputToValue WriteSuccessExactTransactionsRecipientAbsentToValue.

Definition transactionRecipientAccessMemory `{!islaG Sigma} `{!threadG}
    (sp tag first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 120) ↦ₘ tag ∗
   (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAccessMemory) := I.

Lemma transactions_recipient_exit_access_memory `{!islaG Sigma} `{!threadG}
    (sp tag first second : bv 64) (last : bv 32) (P : iProp Sigma) :
  transactionRecipientValueExitFrame sp tag first second last P -∗
  transactionRecipientAccessMemory sp tag first second last P.
Proof.
  unfold transactionRecipientValueExitFrame. destruct (bool_decide (tag = BV 64 0)).
  - iIntros "(Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Halign & Hlow & Hhigh & Hcaller & _)".
    iDestruct "Hcaller" as "(Htag & HP & _)".
    unfold transactionRecipientAccessMemory. iFrame.
  - iIntros "(Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & %Halign & %Hlow & %Hhigh & Hcaller & _)".
    iDestruct "Hcaller" as "(Htag & HP & _)".
    iPoseProof (byte_array_forget with "Hdestination") as "Hscratch".
    have Haddress : bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744 by bv_solve.
    have Hlen : length (words_20_payload first second last) = 20%nat by reflexivity.
    iEval (rewrite Hlen /= Haddress) in "Hscratch".
    unfold transactionRecipientAccessMemory. iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_recipient_exit_access_memory.
