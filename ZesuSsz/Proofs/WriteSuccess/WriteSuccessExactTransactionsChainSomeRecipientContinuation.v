Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsChainSomeToPrice
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsGasRecipientSource
  WriteSuccessExactTransactionsNonceRecipientRegion WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsRecipientDataAccessRegion WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsAccessCountCall
  WriteSuccessExactTransactionsChainToNonce WriteSuccessExactOptionalU64SomeBooleanResume
  WriteSuccessExactOptionalU64SomeJumpHandoff.

Lemma transactions_chain_some_recipient_continuation `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count : bv 64) (last : bv 32) dataBytes chainBytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)))))) -∗
  □ instr_pre 0x150fc (optionalU64SomeExactPost sp (BV 64 0x150fc) data
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value
      (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
        (transactionDataAccessOutputTrace data size sp count dataBytes tail)))
    (optionalU64SomeExactSourceFrame (sp + BV 64 1664)%bv chainBytes
      (transactionChainNonceCaller sp nonce
        (transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow feeHigh value
          tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes P)))).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_nonce_recipient_region_correct sp nonce gaslow gashigh feeTag feeLow feeHigh
    value tag first second w0 w1 w2 w3 (BV 64 0x150fc) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 8)
    old12 old13 data size count (BV 64 0x15bfc) last dataBytes tail
    (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)%I
    with "Hcode Hnext") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hcallee"); [done | done |].
  iApply transactions_chain_some_to_nonce_price.
Qed.
Print Assumptions transactions_chain_some_recipient_continuation.
