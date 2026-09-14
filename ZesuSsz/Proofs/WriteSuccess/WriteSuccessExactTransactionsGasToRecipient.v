Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasRecipientSource
  WriteSuccessExactTransactionsGasLimitCall WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsNonceToGasPrice
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessExactTransactionsRecipientBranch WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsValueDataAccessContinuation WriteSuccessExactTransactionsDataToAccessCount.

Definition transactionGasRecipientSourceCaller `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 old12 old13 data size count old6 : bv 64)
    (last : bv 32) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits data ∗ "x6" ↦ᵣ RVal_Bits old6 ∗
   transactionGasRecipientSourceCore sp tag first second w0 w1 w2 w3 old12 old13
     data size count last bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasRecipientSourceCaller) := I.

Definition transactionGasRecipientCarry `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag high value nonce : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x26" ↦ᵣ RVal_Bits value ∗ "x27" ↦ᵣ RVal_Bits tag ∗ "x23" ↦ᵣ RVal_Bits high ∗
   transactionGasPriceFrame sp gaslow gashigh (transactionNonceGasPriceFrame sp nonce P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasRecipientCarry) := I.

Lemma transactions_gas_limit_to_recipient `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh feeTag feeLow feeHigh value nonce tag first second w0 w1 w2 w3
      old12 old13 data size count old6 : bv 64) (last : bv 32) bytes tail (P : iProp Sigma) :
  transactionGasLimitPost sp value
    (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
      (transactionDataAccessOutputTrace data size sp count bytes tail))
    (transactionFeeGasLimitFrame sp gaslow gashigh feeTag feeLow feeHigh
      (transactionNonceGasPriceFrame sp nonce
        (transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13
          data size count old6 last bytes P))) -∗
  transactionRecipientBranchState sp tag (sp - BV 64 16)%bv
    (transactionRecipientBranchCallerFrame sp tag first second w0 w1 w2 w3
      (BV 64 0x15154) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 8) old12 old13 last
      (transactionDataAccessOutputTrace data size sp count bytes tail)
      (transactionValueDataAccessCaller data size sp count old6 feeLow bytes
        (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce P))).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hgas & _)".
  iDestruct "Hgas" as "(H26 & %HgasAlign & %HgasLow & %HgasHigh & Hfee & _)".
  iDestruct "Hfee" as "(H27 & H9 & H23 & Hmiddle & Hprice & _)".
  iDestruct "Hprice" as "(H24 & H25 & %HpriceAlign & %HpriceLow & %HpriceHigh & Hnonce & _)".
  iDestruct "Hnonce" as "(HnonceMemory & %HnonceAlign & %HnonceLow & %HnonceHigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & H6 & Hcore & _)".
  iDestruct "Hcore" as "(H12 & H13 & H18 & H20 & Hword2 & H21 & Htag & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hlower & H22 & HdataBytes & %Hlen & Hcount & %Halign & %Hlow & %Hhigh & HP & _)".
  iAssert ((bv_unsigned sp - 32) ↦ₘ? 32)%I with "[Hmiddle Hupper]" as "Hscratch32".
  { iApply (mem_mapsto_uninit_combine 16 with "Hmiddle"); first lia.
    replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia. iExact "Hupper". }
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hlower Hscratch32]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 16 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. iExact "Hscratch32". }
  unfold transactionRecipientBranchState, transactionRecipientBranchCallerFrame,
    transactionValueDataAccessCaller, transactionDataAccessCaller,
    transactionGasRecipientCarry, transactionGasPriceFrame, transactionNonceGasPriceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; first [lia | bv_solve].
Qed.
Print Assumptions transactions_gas_limit_to_recipient.
