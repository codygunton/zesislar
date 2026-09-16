Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsOptionPrefix WriteSuccessExactTransactionsOptionValues
  WriteSuccessExactTransactionsFlagLoads.

Definition transactionOptionValuesCaller `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
    ["x28"; "x29"; "x30"; "x31"; "x18"]) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionValuesCaller) := I.

Definition transactionOptionPrefixRetained `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x16" ↦ᵣ RVal_Bits (transactionRowByte bytes index 283) ∗
   "x17" ↦ᵣ RVal_Bits (transactionRowByte bytes index 284) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   "x6" ↦ᵣ RVal_Bits (transactionRowByte bytes index 273) ∗
   "x7" ↦ᵣ RVal_Bits (transactionRowByte bytes index 274) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionPrefixRetained) := I.

Lemma transactions_option_values_entry `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  transactionOptionPrefixPost row base bytes index (transactionOptionValuesCaller P) -∗
  transactionOptionValuesEntry row base bytes index (transactionOptionPrefixRetained bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionOptionPrefixPost /transactionOptionValuesCaller) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H16 & H17 & H5 & H6 & H7 & Hrow & Hbytes & %Hcursor &
    %Hlength & %Hlow & %Hhigh & (Hregs & HP & _) & _)".
  rewrite /transactionOptionValuesEntry /transactionOptionPrefixRetained.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_option_values_entry.

Lemma transactions_option_sources_region_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f90 (transactionOptionValuesPost row base bytes index
    (transactionOptionPrefixRetained bytes index P)) -∗
  instr_body 0x14f68 (transactionOptionPrefixEntry row base bytes index
    (transactionOptionValuesCaller P)).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof (transactions_option_values_correct row base bytes index
    (transactionOptionPrefixRetained bytes index P) with "Hcode Hnext") as "Hvalues".
  iApply (transactions_option_prefix_correct row base bytes index
    (transactionOptionValuesCaller P) with "Hcode").
  iApply (instr_pre_wand 0x14f7c 0x14f7c false false with "Hvalues"); [done | done |].
  iApply transactions_option_values_entry.
Qed.
Print Assumptions transactions_option_sources_region_correct.

