Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsChainSomeRegion WriteSuccessExactTransactionsChainSomeCaller
  WriteSuccessExactTransactionsAccessCountCallerFrame WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactAccessListsRegion WriteSuccessExactAccessListsReturnCount WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsChainToNonce
  WriteSuccessExactTransactionsDataToAccessCount WriteSuccessExactTransactionsValueToData
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessAccessListsSpec WriteSuccessExactAccessListsSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_chain_some_access_region_correct `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count oldra olddata old5 old6 old11 chainvalue x19 savedX22 : bv 64)
    (chainTag : bv 8) (last : bv 32) dataBytes chainBytes base entries accessBytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (accessReturnCountPost sp savedX22 tail
    (accessReturnLoopFrame sp base entries accessBytes x19
      (transactionAccessRetainedMemory sp tag first second w2 data last dataBytes (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)%I))) -∗
  instr_body 0x150f0 (transactionChainSomeCaller chainvalue sp oldra olddata old5 old6 data old11 chainTag chainBytes
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value
      (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
        (transactionDataAccessOutputTrace data size sp count dataBytes (writeSuccessExactAccessListsEvents sp entries
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)))))
    (transactionChainNonceCaller sp nonce
      (transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow feeHigh value
        tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P)))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (access_exact_initial_region_correct sp base entries accessBytes nonce x19 savedX22
    (sp - BV 64 16)%bv (BV 64 8) size feeTag tail
    (transactionAccessRetainedMemory sp tag first second w2 data last dataBytes (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)%I)
    with "Hcode Hnext") as "Haccess".
  iAssert (□ instr_pre 0x151d0 (transactionAccessCountPost sp count (writeSuccessExactAccessListsEvents sp entries
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P ∗ True)%I))))))%I as "#HcountNext".
  { iModIntro. iApply (instr_pre_wand 0x151d0 0x151d0 false true with "Haccess"); [done | done |].
    iIntros "Hpost".
    iApply (transactions_data_to_access_entry sp nonce gaslow gashigh feeTag feeLow feeHigh value
      tag first second w0 w1 w2 w3 data size count x19 savedX22 last dataBytes base entries accessBytes tail
      (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)%I).
    iEval (rewrite (transactions_access_count_caller_frame sp nonce gaslow gashigh feeTag feeLow feeHigh value
      tag first second w0 w1 w2 w3 data size count x19 savedX22 last dataBytes base entries accessBytes
      (writeSuccessExactAccessListsEvents sp entries (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))
      (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes)%I P)) in "Hpost".
    iExact "Hpost". }
  iApply (transactions_chain_some_region_correct sp nonce gaslow gashigh feeTag feeLow feeHigh value
    tag first second w0 w1 w2 w3 old12 old13 data size count oldra olddata old5 old6 old11 chainvalue
    chainTag last dataBytes chainBytes
    (writeSuccessExactAccessListsEvents sp entries (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))
    (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P)
    with "Hcode HcountNext").
Qed.
Print Assumptions transactions_chain_some_access_region_correct.

