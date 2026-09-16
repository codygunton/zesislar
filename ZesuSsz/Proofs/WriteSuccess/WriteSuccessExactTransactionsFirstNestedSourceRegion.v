Require Import ZesuSsz.Automation.AllLegacy.
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
  WriteSuccessExactTransactionsFirstRecipientWordsRegion WriteSuccessExactTransactionsRecipientWordsSignatureValuesEntry
  WriteSuccessExactTransactionsSignatureValues
  WriteSuccessExactTransactionsFirstSignatureValuesRegion WriteSuccessExactTransactionsSignatureLowWideEntry
  WriteSuccessExactTransactionsRecipientLowWords WriteSuccessExactTransactionsRecipientWide
  WriteSuccessExactTransactionsFirstRecipientWideRegion WriteSuccessExactTransactionsWideSignatureSuffixEntry
  WriteSuccessExactTransactionsSignatureSuffix WriteSuccessExactTransactionsSignatureTail
  WriteSuccessExactTransactionsFirstSignatureTailRegion WriteSuccessExactTransactionsNestedSourceEntry
  WriteSuccessExactTransactionsNestedLists WriteSuccessExactTransactionsNestedSuffix
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_nested_source_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x150cc (transactionNestedSuffixPost sp row base bytes index
    (transactionNestedSuffixRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp (transactionValuePrefixCaller (transactionRecipientMiddlePairCaller sp (transactionSignatureValuesCaller sp
            (transactionSignatureSuffixCaller sp (transactionSignatureTailCaller sp
              (transactionNestedListsCaller sp (transactionNestedSuffixCaller sp P))))))))) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  pose (recipient := Z_to_bv 64 (little_endian_to_bv 8
    [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])).
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_33.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#HtailCode".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_nested_suffix_correct sp row base bytes index
    (transactionNestedSuffixRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) bytes index P)
    with "HtailCode Hnext") as "Hsuffix".
  iAssert (instr_body 0x150b0 (transactionNestedListsPost sp row recipient base bytes index
    (transactionNestedListsRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) bytes index (transactionNestedSuffixCaller sp P))))
    with "[Hsuffix]" as "HlistsNext".
  { iApply (instr_pre_wand 0x150b0 0x150b0 false false with "Hsuffix"); [done | done |].
    iApply transactions_nested_lists_suffix_entry. }
  iPoseProof (transactions_nested_lists_correct sp row recipient base bytes index
    (transactionNestedListsRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) bytes index (transactionNestedSuffixCaller sp P))
    with "HtailCode HlistsNext") as "Hlists".
  iApply (transactions_first_signature_tail_region_correct sp row base bytes index
    (transactionNestedListsCaller sp (transactionNestedSuffixCaller sp P)) with "Hcode").
  iApply (instr_pre_wand 0x15098 0x15098 false false with "Hlists"); [done | done |].
  iApply transactions_signature_tail_nested_lists_entry.
Qed.
Print Assumptions transactions_first_nested_source_region_correct.

