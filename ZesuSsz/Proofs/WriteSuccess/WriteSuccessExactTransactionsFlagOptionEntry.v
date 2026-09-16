Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactTransactionsOptionPrefix
  WriteSuccessExactTransactionsFieldFlagEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads.

Definition transactionFirstLoadRetained `{!islaG Sigma} `{!threadG}
    sp row bytes index (P : iProp Sigma) : iProp Sigma :=
  transactionFieldFlagRetained sp bytes index
    (transactionSignatureFieldRetained sp row bytes index
      (transactionGasSignatureRetained sp bytes index P)).
Global Instance : LithiumUnfold (@transactionFirstLoadRetained) := I.

Definition transactionFlagOptionRetained `{!islaG Sigma} `{!threadG}
    (row : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   "x14" ↦ᵣ RVal_Bits (transactionRowByte bytes index 281) ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 282) ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFlagOptionRetained) := I.

Lemma transactions_flag_option_entry `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  transactionFlagLoadPost row base bytes index
    (transactionFirstLoadRetained sp row bytes index
      (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
        ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗ P ∗ True)%I) -∗
  transactionOptionPrefixEntry row base bytes index
    (transactionFlagOptionRetained row bytes index
      (transactionFirstLoadRetained sp row bytes index P)).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionFlagLoadPost /transactionFirstLoadRetained
    /transactionFieldFlagRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H13 & H14 & H15 & Hrow & Hbytes & %Hcursor & %Hlength &
    %HbaseLow & %HbaseHigh & (Hsp & H11 & H12 & H26 & H8 & Hnonce & %HspAlign & %HspLow &
    %HspHigh & (H152 & H144 & H136 & %HrowAlign & %HrowLength & %HstackHigh &
    (H25 & H24 & H9 & H23 & %HrowLength2 & %HstackHigh2 & (Hothers & HP & _) & _) & _) & _) & _)".
  rewrite /transactionOptionPrefixEntry /transactionFlagOptionRetained /transactionFirstLoadRetained
    /transactionFieldFlagRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_flag_option_entry.

