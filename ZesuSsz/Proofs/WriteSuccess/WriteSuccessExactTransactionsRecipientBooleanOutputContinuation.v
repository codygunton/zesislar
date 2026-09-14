Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientBooleanToOutput
  WriteSuccessExactTransactionsRecipientCopyToBoolean WriteSuccessExactTransactionsRecipientOutput
  WriteSuccessExactBooleanSpec.

Lemma transactions_recipient_boolean_output_continuation `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15190 (transactionRecipientOutputPost sp
    (words_20_payload first second last) tail
    (transactionRecipientOutputCallerFrame sp first second last P)) -∗
  □ instr_pre 0x15180 (encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15180)
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
      (words_20_payload first second last) tail)
    (transactionRecipientCopiedFrame sp first second last P)).
Proof.
  iIntros "#Hcode #Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_recipient_output_call_correct sp (BV 64 0x15180)
    (BV 64 (mapIoContextAddress defaultMap)) (sp - BV 64 9)%bv (BV 64 1)
    (words_20_payload first second last) tail
    (transactionRecipientOutputCallerFrame sp first second last P)
    with "[] Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iModIntro. iApply (instr_pre_wand 0x15180 0x15180 false true with "Hcallee"); [done | done |].
  iIntros "Hpost".
  iSplitL "Hpost"; first (iApply transactions_recipient_boolean_to_output; iExact "Hpost").
  iFrame "Hnext".
Qed.
Print Assumptions transactions_recipient_boolean_output_continuation.
