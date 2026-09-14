Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsRecipientLoads
  WriteSuccessExactTransactionsRecipientPair WriteSuccessExactTransactionsFlagOptionEntry
  WriteSuccessExactTransactionsOptionSourcesRegion WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsLayout.
Local Open Scope Z_scope.

Definition transactionRecipientPairSourceFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) base bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits (transactionRowByte bytes index 266) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 267) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 1664) ↦ₘ chain ∗
   (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜(bv_unsigned sp `mod` 8 = 0)%Z⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1680 < 0x40000000)%Z⌝ ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   ⌜(bv_unsigned row `mod` 8 = 0)%Z⌝ ∗ transactionFirstRecipientTail sp row bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairSourceFrame) := I.

Lemma transactions_recipient_source_pair_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientLoadPost sp row chain chainTag base bytes index
    (transactionFirstRecipientRetained sp row bytes index P) -∗
  transactionRecipientPairEntry
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (transactionRecipientPairSourceFrame sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientLoadPost /transactionFirstRecipientRetained
    /transactionFlagOptionRetained /transactionFirstRecipientTail /transactionOptionPrefixRetained
    /transactionSignatureFieldRetained /transactionGasSignatureRetained) in "Hpost".
  zesu_open_resource_groups.
  have H281 : transactionRowByte bytes index 281 =
    bv_zero_extend 64 (default (BV 8 0) (bytes !! (index + 281)%nat)).
  { apply exact_transaction_row_byte_extend. lia. }
  have H282 : transactionRowByte bytes index 282 =
    bv_zero_extend 64 (default (BV 8 0) (bytes !! (index + 282)%nat)).
  { apply exact_transaction_row_byte_extend. lia. }
  iSelect ("x14" ↦ᵣ _)%I ltac:(fun Hreg => iEval (rewrite H281) in Hreg).
  iSelect ("x15" ↦ᵣ _)%I ltac:(fun Hreg => iEval (rewrite H282) in Hreg).
  rewrite /transactionRecipientPairEntry /transactionRecipientPairSourceFrame /transactionFirstRecipientTail
    /transactionOptionPrefixRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_source_pair_entry.

