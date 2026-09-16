Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientAbsentToValue
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec
  WriteSuccessExactBooleanSpec.

Lemma transactions_recipient_absent_value_continuation `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 old12 old13 : bv 64) (last : bv 32)
    tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientAbsentValueSourceFrame sp first second last P)) -∗
  □ instr_pre 0x1519c (encoderBooleanExactPost (BV 64 0) sp (BV 64 0x1519c)
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)
    (transactionRecipientAbsentValuePreparation sp first second w0 w1 w2 w3 old12 old13 last P)).
Proof.
  iIntros "#Hcode #Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_value_call_correct sp w0 w1 w2 w3 (BV 64 0x1519c)
    (BV 64 (mapIoContextAddress defaultMap)) tail (transactionRecipientAbsentValueSourceFrame sp first second last P)
    with "[] Hu256 Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iModIntro. iApply (instr_pre_wand 0x1519c 0x1519c false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_recipient_absent_boolean_to_value with "Hpost Hnext").
Qed.
Print Assumptions transactions_recipient_absent_value_continuation.
