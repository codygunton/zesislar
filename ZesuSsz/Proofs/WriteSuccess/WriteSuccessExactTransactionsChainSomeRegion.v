Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsChainSomeToPrice
  WriteSuccessExactTransactionsChainSomeCaller WriteSuccessExactTransactionsChainSomeCall
  WriteSuccessExactTransactionsChainSomeRecipientContinuation
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsGasRecipientSource
  WriteSuccessExactTransactionsNonceRecipientRegion WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsRecipientDataAccessRegion WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsAccessCountCall
  WriteSuccessExactTransactionsChainToNonce WriteSuccessExactOptionalU64SomeBooleanResume
  WriteSuccessExactOptionalU64SomeJumpHandoff.


Lemma transactions_chain_some_region_correct `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count oldra olddata old5 old6 old11 chainvalue : bv 64)
    (chainTag : bv 8)
    (last : bv 32) dataBytes chainBytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗ P ∗ True)))))) -∗
  instr_body 0x150f0 (transactionChainSomeCaller chainvalue sp oldra olddata old5 old6 data old11 chainTag chainBytes
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value
      (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
        (transactionDataAccessOutputTrace data size sp count dataBytes tail)))
    (transactionChainNonceCaller sp nonce
      (transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow feeHigh value
         tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes P))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_chain_some_recipient_continuation sp nonce gaslow gashigh feeTag feeLow feeHigh
    value tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes chainBytes tail P
    with "Hcode Hnext") as "Hreturn".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_35.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hcaller".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iPoseProof (transactions_chain_some_call_correct chainvalue sp oldra olddata old5 old6 data old11 chainTag chainBytes
    (transactionNoncePricePriorityOutputTrace sp nonce gaslow gashigh feeTag feeLow feeHigh value
      (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
        (transactionDataAccessOutputTrace data size sp count dataBytes tail)))
    (transactionChainNonceCaller sp nonce
      (transactionChainPriceRecipientCaller sp gaslow gashigh feeTag feeLow
        feeHigh value tag first second w0 w1 w2 w3 old12 old13 data size count last dataBytes P))%I
    with "Hcaller Hoptional Hboolean Hint Houtput") as "Hnative".
  iApply (instr_pre_wand 0x150f0 0x150f0 false false with "Hnative"); [done | done |].
  iApply (transactions_chain_some_caller_entry with "Hreturn").
Qed.
Print Assumptions transactions_chain_some_region_correct.
