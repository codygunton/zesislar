Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactTransactionsNonceRecipientRegion WriteSuccessExactTransactionsNoncePricePriorityRegion
  WriteSuccessExactTransactionsGasToRecipient WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientValueRegion
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactAccessListsRegion
  WriteSuccessExactAccessListsReturnCount WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessAccessListsSpec WriteSuccessExactAccessListsSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_nonce_access_region_correct `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 data size count old6 x19 savedX22 : bv 64)
    (last : bv 32) dataBytes base entries accessBytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (accessReturnCountPost sp savedX22 tail
    (accessReturnLoopFrame sp base entries accessBytes x19
      (transactionAccessRetainedMemory sp tag first second w2 data last dataBytes P))) -∗
  instr_body 0x150fc (transactionNoncePricePriorityEntry sp nonce gaslow gashigh feeTag feeLow feeHigh
    value oldra old5 old11
    (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
      (transactionDataAccessOutputTrace data size sp count dataBytes
        (writeSuccessExactAccessListsEvents sp entries
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
            (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))))
    (transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13
      data size count old6 last dataBytes
      (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (access_exact_initial_region_correct sp base entries accessBytes nonce x19 savedX22
    (sp - BV 64 16)%bv (BV 64 8) size feeTag tail
    (transactionAccessRetainedMemory sp tag first second w2 data last dataBytes P)
    with "Hcode Hnext") as "Haccess".
  iAssert (□ instr_pre 0x151d0 (transactionAccessCountPost sp count
    (writeSuccessExactAccessListsEvents sp entries
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P)))))))%I
    as "#HaccessNext".
  { iModIntro. iApply (instr_pre_wand 0x151d0 0x151d0 false true with "Haccess"); [done | done |].
    iApply transactions_data_to_access_entry. }
  iApply (transactions_nonce_recipient_region_correct with "Hcode HaccessNext").
Qed.
Print Assumptions transactions_nonce_access_region_correct.
