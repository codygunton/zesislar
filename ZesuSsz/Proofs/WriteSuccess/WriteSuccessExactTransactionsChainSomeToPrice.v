Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsGasRecipientSource WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsNoncePricePriorityRegion WriteSuccessExactTransactionsNonceToGasPrice
  WriteSuccessExactTransactionsPriorityGasRegion WriteSuccessExactTransactionsChainToNonce
  WriteSuccessExactOptionalU64SomeBooleanResume WriteSuccessExactOptionalU64SomeJumpHandoff
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactEncoderU128
  WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_chain_some_to_nonce_price `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count : bv 64) (last : bv 32) dataBytes chainBytes tail (P : iProp Sigma) :
  optionalU64SomeExactPost sp (BV 64 0x150fc) data
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value tail)
    (optionalU64SomeExactSourceFrame (sp + BV 64 1664)%bv chainBytes
      (transactionChainNonceCaller sp nonce
        (transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow feeHigh value
          tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes P))) -∗
  transactionNoncePricePriorityEntry sp nonce gaslow gashigh feeTag feeLow feeHigh value
    (BV 64 0x150fc) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 8) tail
    (transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13 data size count
      (BV 64 0x15bfc) last dataBytes (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H6 & H8 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(HchainBytes & Hnonce & _)".
  iDestruct "Hnonce" as "(HnonceMemory & %HnonceAlign & %HnonceLow & %HnonceHigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H24 & H25 & H27 & H9 & H23 & H26 & Hcore & _)".
  iDestruct "Hcore" as "(H12 & H13 & H18 & H20 & Hword2 & H21 & Htag & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hlower & H22 & HdataBytes & %Hlen & Hcount & %Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hmiddle Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)])%I with "[H10]" as "Hargs".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionNoncePricePriorityEntry, transactionNoncePricePriorityFrame,
    transactionNonceGasPriceCaller, transactionGasRecipientSourceCaller, transactionGasRecipientSourceCore.
  iEval (rewrite /transactionNoncePricePriorityOutputTrace) in "Htrace".
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_chain_some_to_nonce_price.
