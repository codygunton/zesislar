Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsFirstLoadsRegion
  WriteSuccessExactTransactionsFlagOptionEntry WriteSuccessExactTransactionsFlagOptionCallerFrame
  WriteSuccessExactTransactionsOptionSourcesRegion WriteSuccessExactTransactionsOptionPrefix
  WriteSuccessExactTransactionsOptionValues WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsSignatureFieldEntry.

Local Instance transaction_option_prefix_entry_proper `{!islaG Sigma} `{!threadG} row base bytes index :
  Proper (equiv ==> equiv) (transactionOptionPrefixEntry row base bytes index).
Proof. intros P Q HPQ. unfold transactionOptionPrefixEntry. by rewrite HPQ. Qed.

Lemma transactions_first_sources_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x14f90 (transactionOptionValuesPost row base bytes index
    (transactionOptionPrefixRetained bytes index
      (transactionFlagOptionRetained row bytes index
        (transactionFirstLoadRetained sp row bytes index P)))) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗ transactionOptionValuesCaller P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hloads".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#HoptionCode".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_option_sources_region_correct row base bytes index
    (transactionFlagOptionRetained row bytes index (transactionFirstLoadRetained sp row bytes index P))
    with "HoptionCode Hnext") as "Hoptions".
  iApply (transactions_first_loads_region_correct sp row base bytes index
    (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗ transactionOptionValuesCaller P ∗ True)%I with "Hloads").
  iApply (instr_pre_wand 0x14f68 0x14f68 false false with "Hoptions"); [done | done |].
  iIntros "Hpost".
  iPoseProof (transactions_flag_option_entry sp row base bytes index (transactionOptionValuesCaller P)
    with "Hpost") as "Hentry".
  iEval (rewrite transactions_flag_option_caller_frame) in "Hentry". iExact "Hentry".
Qed.
Print Assumptions transactions_first_sources_region_correct.

