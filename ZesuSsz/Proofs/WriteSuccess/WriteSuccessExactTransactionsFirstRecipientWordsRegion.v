Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsFirstSourcesRegion
  WriteSuccessExactTransactionsFirstRecipientRegion
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsRecipientLoads
  WriteSuccessExactTransactionsRecipientSourcePairEntry WriteSuccessExactTransactionsRecipientPair
  WriteSuccessExactTransactionsFirstRecipientPairRegion WriteSuccessExactTransactionsRecipientPairTagEntry
  WriteSuccessExactTransactionsToTag
  WriteSuccessExactTransactionsFirstRecipientTagRegion WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsRecipientShifts
  WriteSuccessExactTransactionsFirstRecipientShiftsRegion WriteSuccessExactTransactionsRecipientShiftsHighEntry
  WriteSuccessExactTransactionsRecipientHighShifts
  WriteSuccessExactTransactionsFirstRecipientHighRegion WriteSuccessExactTransactionsRecipientHighPairsEntry
  WriteSuccessExactTransactionsRecipientPairs
  WriteSuccessExactTransactionsFirstRecipientPairsRegion WriteSuccessExactTransactionsRecipientPairsMiddleEntry
  WriteSuccessExactTransactionsRecipientMiddle
  WriteSuccessExactTransactionsFirstRecipientMiddleRegion WriteSuccessExactTransactionsRecipientMiddleLowerEntry
  WriteSuccessExactTransactionsRecipientLowerShifts
  WriteSuccessExactTransactionsFirstRecipientLowerShiftsRegion
  WriteSuccessExactTransactionsRecipientLowerShiftsPairsEntry WriteSuccessExactTransactionsRecipientLowerPairs
  WriteSuccessExactTransactionsFirstRecipientLowerPairsRegion WriteSuccessExactTransactionsRecipientLowerPairsValueEntry
  WriteSuccessExactTransactionsValuePrefix
  WriteSuccessExactTransactionsFirstValuePrefixRegion WriteSuccessExactTransactionsValueMiddleWordsEntry
  WriteSuccessExactTransactionsRecipientMiddlePair WriteSuccessExactTransactionsRecipientWords
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_recipient_words_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15044 (transactionRecipientWordsPost
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWordsRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp (transactionValuePrefixCaller (transactionRecipientMiddlePairCaller sp P)))) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_recipient_words_correct
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWordsRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller Hnext") as "Hwords".
  iAssert (instr_body 0x15038 (transactionRecipientMiddlePairPost sp
    (transactionRowWord bytes index 64) (default (BV 8 0) (bytes !! (index + 271)%nat)) (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientMiddlePairFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P))) with "[Hwords]" as "HmiddleNext".
  { iApply (instr_pre_wand 0x15038 0x15038 false false with "Hwords"); [done | done |].
    iApply transactions_middle_pair_words_entry. }
  iPoseProof (transactions_recipient_middle_pair_correct sp
    (transactionRowWord bytes index 64) (default (BV 8 0) (bytes !! (index + 271)%nat)) (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientMiddlePairFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller HmiddleNext") as "Hmiddle".
  iApply (transactions_first_value_prefix_region_correct sp row base bytes index
    (transactionRecipientMiddlePairCaller sp P) with "Hcode").
  iApply (instr_pre_wand 0x15028 0x15028 false false with "Hmiddle"); [done | done |].
  iApply transactions_value_prefix_middle_pair_entry.
Qed.
Print Assumptions transactions_first_recipient_words_region_correct.

