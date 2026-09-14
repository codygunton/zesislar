Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsChainNoneToPrice
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsGasRecipientSource
  WriteSuccessExactTransactionsNonceRecipientRegion WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsRecipientDataAccessRegion WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsAccessCountCall
  WriteSuccessExactTransactionsChainToNonce WriteSuccessExactOptionalU64NoneCallSpec.

Lemma transactions_chain_none_recipient_continuation `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count : bv 64) (last : bv 32) dataBytes chainBytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)))))) -∗
  □ instr_pre 0x150fc (optionalU64NoneExactCallPost (sp + BV 64 1664)%bv sp (BV 64 0x150fc) chainBytes
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value
      (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
        (transactionDataAccessOutputTrace data size sp count dataBytes tail)))
    (transactionChainNonceCaller sp nonce
      ("x8" ↦ᵣ RVal_Bits data ∗
       transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow feeHigh value
         tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes P ∗ True))).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_nonce_recipient_region_correct sp nonce gaslow gashigh feeTag feeLow feeHigh
    value tag first second w0 w1 w2 w3 (BV 64 0x150fc) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 1)
    old12 old13 data size count (BV 64 0x15c08) last dataBytes tail
    (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)%I
    with "Hcode Hnext") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hcallee"); [done | done |].
  iApply transactions_chain_none_to_nonce_price.
Qed.
Print Assumptions transactions_chain_none_recipient_continuation.
