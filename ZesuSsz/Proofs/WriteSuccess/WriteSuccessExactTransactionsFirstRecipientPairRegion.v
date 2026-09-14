Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsFirstSourcesRegion
  WriteSuccessExactTransactionsFirstRecipientRegion
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsRecipientLoads
  WriteSuccessExactTransactionsRecipientSourcePairEntry WriteSuccessExactTransactionsRecipientPair
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_recipient_pair_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x14fb0 (transactionRecipientPairPost
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (transactionRecipientPairSourceFrame sp row
      (transactionRowWord bytes index 160) (transactionRowWord bytes index 168) base bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp P) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_recipient_pair_correct
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (transactionRecipientPairSourceFrame sp row
      (transactionRowWord bytes index 160) (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller Hnext") as "Hpair".
  iApply (transactions_first_recipient_region_correct sp row base bytes index P with "Hcode").
  iApply (instr_pre_wand 0x14fa8 0x14fa8 false false with "Hpair"); [done | done |].
  iApply transactions_recipient_source_pair_entry.
Qed.
Print Assumptions transactions_first_recipient_pair_region_correct.

