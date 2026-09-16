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
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_recipient_wide_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15078 (transactionRecipientWidePost
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (default (BV 8 0) (bytes !! (index + 271)%nat))
    (default (BV 8 0) (bytes !! (index + 272)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWideFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp (transactionValuePrefixCaller (transactionRecipientMiddlePairCaller sp (transactionSignatureValuesCaller sp P))))) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  pose (byte := fun offset : nat => default (BV 8 0) (bytes !! (index + offset)%nat)).
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_recipient_wide_correct
    (byte 265%nat) (byte 266%nat) (byte 267%nat) (byte 268%nat)
    (byte 269%nat) (byte 270%nat) (byte 271%nat) (byte 272%nat)
    (byte 273%nat) (byte 274%nat) (byte 275%nat) (byte 276%nat)
    (byte 277%nat) (byte 278%nat) (byte 279%nat) (byte 280%nat)
    (transactionRecipientWideFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller Hnext") as "Hwide".
  iAssert (instr_body 0x15068 (transactionRecipientLowWordsPost
    (byte 265%nat) (byte 266%nat) (byte 267%nat) (byte 268%nat)
    (byte 269%nat) (byte 270%nat) (byte 271%nat) (byte 272%nat)
    (transactionRecipientLowWordsFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P))) with "[Hwide]" as "HlowNext".
  { iApply (instr_pre_wand 0x15068 0x15068 false false with "Hwide"); [done | done |].
    iApply transactions_recipient_low_words_wide_entry. }
  iPoseProof (transactions_recipient_low_words_correct
    (byte 265%nat) (byte 266%nat) (byte 267%nat) (byte 268%nat)
    (byte 269%nat) (byte 270%nat) (byte 271%nat) (byte 272%nat)
    (transactionRecipientLowWordsFrame sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller HlowNext") as "Hlow".
  iApply (transactions_first_signature_values_region_correct sp row base bytes index P with "Hcode").
  iApply (instr_pre_wand 0x15060 0x15060 false false with "Hlow"); [done | done |].
  iApply transactions_signature_values_low_words_entry.
Qed.
Print Assumptions transactions_first_recipient_wide_region_correct.
