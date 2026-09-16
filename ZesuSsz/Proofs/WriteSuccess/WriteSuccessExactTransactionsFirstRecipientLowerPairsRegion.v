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
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_recipient_lower_pairs_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15018 (transactionRecipientLowerPairsPost
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (transactionRecipientLowerPairRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp P)) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_recipient_lower_pairs_correct
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (transactionRecipientLowerPairRetained sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index P)
    with "Hcaller Hnext") as "Hpairs".
  iApply (transactions_first_recipient_lower_shifts_region_correct sp row base bytes index P with "Hcode").
  iApply (instr_pre_wand 0x15008 0x15008 false false with "Hpairs"); [done | done |].
  iApply transactions_recipient_lower_shifts_pairs_entry.
Qed.
Print Assumptions transactions_first_recipient_lower_pairs_region_correct.

