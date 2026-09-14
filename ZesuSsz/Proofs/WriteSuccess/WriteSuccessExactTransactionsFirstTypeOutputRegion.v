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

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFirstNestedSourceRegion
  WriteSuccessExactTransactionsPrepareSourceEntry WriteSuccessExactTransactionsPrepare.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFirstPrepareSourceRegion WriteSuccessExactTransactionsTypeSourceEntry
  WriteSuccessExactTransactionsTypeOutput WriteSuccessOutput.
Local Existing Instance subsume_instr_pre_guard_inst | 0.
Lemma transactions_first_type_output_region_correct `{!islaG Sigma} `{!threadG}
    sp row oldra base bytes index tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x150f0 (transactionTypeOutputPost (sp + BV 64 1744)%bv (default (BV 8 0) (bytes !! (index + 264)%nat)) tail
    (transactionTypeSourceRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp (transactionValuePrefixCaller (transactionRecipientMiddlePairCaller sp (transactionSignatureValuesCaller sp
            (transactionSignatureSuffixCaller sp (transactionSignatureTailCaller sp
              (transactionNestedListsCaller sp (transactionNestedSuffixCaller sp (transactionPrepareCaller sp (transactionTypeSourceCaller sp oldra (default (BV 8 0) (bytes !! (index + 264)%nat)) tail P))))))))))) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_34.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iAssert (□ instr_pre 0x10190
    (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 1) (BV 64 0x150f0)
      [(default (BV 8 0) (bytes !! (index + 264)%nat))] tail (transactionTypeSourceRetained sp row (transactionRowWord bytes index 160)
        (transactionRowWord bytes index 168) base bytes index P)))%I as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "Houtput". }
  iPoseProof (transactions_type_output_correct with "Hcaller Hcallee Hnext") as "Htype".
  iApply (transactions_first_prepare_source_region_correct sp row base bytes index
    (transactionTypeSourceCaller sp oldra (default (BV 8 0) (bytes !! (index + 264)%nat)) tail P) with "Hcode").
  iApply (instr_pre_wand 0x150e8 0x150e8 false false with "Htype"); [done | done |].
  iApply transactions_prepare_type_source_entry.
Qed.
Print Assumptions transactions_first_type_output_region_correct.
