Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientSourcePairEntry WriteSuccessExactTransactionsRecipientPair
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsToTag
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactTransactionsOptionSourcesRegion
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry.
Local Open Scope Z_scope.

Definition transactionToTagDestination `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 120) ↦ₘ? 8 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionToTagDestination) := I.

Definition transactionToTagSourceFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
     [default (BV 8 0) (bytes !! (index + 281)%nat);
      default (BV 8 0) (bytes !! (index + 282)%nat)])) ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowByte bytes index 266) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 267) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   (bv_unsigned sp + 1664) ↦ₘ chain ∗ (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   ⌜(bv_unsigned row `mod` 8 = 0)%Z⌝ ∗ transactionFirstRecipientTail sp row bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionToTagSourceFrame) := I.

Lemma transactions_recipient_pair_tag_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientPairPost
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (transactionRecipientPairSourceFrame sp row chain chainTag base bytes index (transactionToTagDestination sp P)) -∗
  transactionToTagEntry sp row base bytes index (transactionToTagSourceFrame sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientPairPost /transactionRecipientPairSourceFrame /transactionToTagDestination) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H14 & H15 & Hframe & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x15", bv_shiftl (bv_zero_extend 64 (default (BV 8 0) (bytes !! (index + 282)%nat))) (BV 64 8))]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionFirstRecipientTail /transactionOptionPrefixRetained
    /transactionSignatureFieldRetained /transactionGasSignatureRetained) in "Hframe".
  zesu_open_resource_groups.
  rewrite /transactionToTagEntry /transactionToTagSourceFrame /transactionFirstRecipientTail
    /transactionOptionPrefixRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_pair_tag_entry.

