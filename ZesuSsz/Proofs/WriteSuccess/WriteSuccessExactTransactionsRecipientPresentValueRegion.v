Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientPresentRegion
  WriteSuccessExactTransactionsRecipientCopy WriteSuccessExactTransactionsRecipientCopyToBoolean
  WriteSuccessExactTransactionsRecipientOutputToValue WriteSuccessExactTransactionsRecipientOutputValueContinuation
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec.

Lemma transactions_recipient_present_value_region_correct `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 oldra old5 old13 : bv 64) (last : bv 32)
    tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientValueSourceFrame sp first second last P)) -∗
  instr_body 0x1515c (transactionRecipientCopyEntry sp first second last
    (transactionRecipientCopyBooleanFrame sp oldra old5
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
        (words_20_payload first second last)
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
          (writeSuccessU256WordsPayload w0 w1 w2 w3) tail))
      (transactionRecipientValuePreparation sp w0 w1 w2 w3 old13 P))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_recipient_output_value_continuation with "Hcode Hnext") as "#HrecipientNext".
  iApply (transactions_recipient_present_region_correct with "Hcode HrecipientNext").
Qed.
Print Assumptions transactions_recipient_present_value_region_correct.
