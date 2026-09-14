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
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion.

Lemma transactions_first_recipient_pairs_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x14fe0 (transactionRecipientPairsPost
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientAssemblyContextNo15 sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index
      (transactionRecipientPairRemainder bytes index (transactionRecipientAssemblyFields sp row bytes index P)))) -∗
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
  iPoseProof (transactions_recipient_pairs_correct
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientAssemblyContextNo15 sp row (transactionRowWord bytes index 160)
      (transactionRowWord bytes index 168) base bytes index
      (transactionRecipientPairRemainder bytes index (transactionRecipientAssemblyFields sp row bytes index P)))
    with "Hcaller Hnext") as "Hpairs".
  iApply (transactions_first_recipient_high_region_correct sp row base bytes index P with "Hcode").
  iApply (instr_pre_wand 0x14fd0 0x14fd0 false false with "Hpairs"); [done | done |].
  iApply transactions_recipient_high_pairs_entry.
Qed.
Print Assumptions transactions_first_recipient_pairs_region_correct.

