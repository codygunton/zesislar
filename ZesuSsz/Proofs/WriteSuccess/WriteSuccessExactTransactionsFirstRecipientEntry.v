Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagOptionEntry WriteSuccessExactTransactionsOptionSourcesRegion
  WriteSuccessExactTransactionsOptionValues WriteSuccessExactTransactionsRecipientLoads
  WriteSuccessExactTransactionsFieldFlagEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.

Definition transactionRecipientSourceCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64)] ∗
   (bv_unsigned sp + 1664) ↦ₘ? 16 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientSourceCaller) := I.

Definition transactionFirstRecipientTail `{!islaG Sigma} `{!threadG}
    sp row bytes index (P : iProp Sigma) : iProp Sigma :=
  transactionOptionPrefixRetained bytes index
      ("x28" ↦ᵣ RVal_Bits (transactionRowByte bytes index 275) ∗
       "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 276) ∗
       "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 277) ∗
       "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 278) ∗
       "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 279) ∗
       "x26" ↦ᵣ RVal_Bits (transactionRowWord bytes index 184) ∗
       "x8" ↦ᵣ RVal_Bits (transactionRowWord bytes index 192) ∗
       (bv_unsigned sp + 272) ↦ₘ (transactionRowWord bytes index 176) ∗
       transactionSignatureFieldRetained sp row bytes index
         (transactionGasSignatureRetained sp bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFirstRecipientTail) := I.

Definition transactionFirstRecipientRetained `{!islaG Sigma} `{!threadG}
    sp row bytes index (P : iProp Sigma) : iProp Sigma :=
  transactionFlagOptionRetained row bytes index (transactionFirstRecipientTail sp row bytes index P).
Global Instance : LithiumUnfold (@transactionFirstRecipientRetained) := I.

Lemma transactions_first_recipient_entry `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  transactionOptionValuesPost row base bytes index
    (transactionOptionPrefixRetained bytes index
      (transactionFlagOptionRetained row bytes index
        (transactionFirstLoadRetained sp row bytes index
          (transactionRecipientSourceCaller sp P)))) -∗
  transactionRecipientLoadEntry sp row
    (transactionRowWord bytes index 160) (transactionRowWord bytes index 168) base bytes index
    (transactionFirstRecipientRetained sp row bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionOptionValuesPost /transactionOptionPrefixRetained
    /transactionFlagOptionRetained /transactionFirstLoadRetained /transactionFieldFlagRetained
    /transactionSignatureFieldRetained /transactionGasSignatureRetained /transactionRecipientSourceCaller) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientLoadEntry /transactionFirstRecipientRetained /transactionFirstRecipientTail /transactionOptionPrefixRetained
    /transactionFlagOptionRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_first_recipient_entry.
