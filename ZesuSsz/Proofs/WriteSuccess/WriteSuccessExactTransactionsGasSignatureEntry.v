Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsSignatureLoads.

Definition transactionGasSignatureCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x11", BitsShape 64)] ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 224) ↦ₘ? 24 ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasSignatureCaller) := I.

Definition transactionGasSignatureRetained `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x25" ↦ᵣ RVal_Bits (transactionRowWord bytes index 0) ∗
   "x24" ↦ᵣ RVal_Bits (transactionRowWord bytes index 8) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowWord bytes index 16) ∗
   "x23" ↦ᵣ RVal_Bits (transactionRowWord bytes index 24) ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasSignatureRetained) := I.

Lemma transactions_gas_signature_entry `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  transactionGasLoadPost row base bytes index (transactionGasSignatureCaller sp bytes index P) -∗
  transactionSignatureLoadEntry sp row base bytes index (transactionGasSignatureRetained sp bytes index P).
Proof.
  iStartProof. iIntros "Hpost". rewrite /transactionGasLoadPost.
  iDestruct "Hpost" as "(Hsys & H25 & H24 & H9 & H23 & Hrow & Hbytes & %Hcursor &
    %Hlength & %Hrowalign & %Hlow & %Hhigh & Hcaller & _)".
  iEval (rewrite /transactionGasSignatureCaller) in "Hcaller".
  iDestruct "Hcaller" as "(Hregs & Hsp & Hscratch & %HrowLength & %Hspalign & %HspLow &
    %HspHigh & HP & _)".
  rewrite /transactionSignatureLoadEntry /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_gas_signature_entry.

