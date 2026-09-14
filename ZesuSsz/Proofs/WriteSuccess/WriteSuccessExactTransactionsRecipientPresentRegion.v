Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientCopy
  WriteSuccessExactTransactionsRecipientCopyToBoolean WriteSuccessExactTransactionsRecipientBooleanCall
  WriteSuccessExactTransactionsRecipientBooleanToOutput WriteSuccessExactTransactionsRecipientOutput
  WriteSuccessExactTransactionsRecipientBooleanOutputContinuation.

Lemma transactions_recipient_present_region_correct `{!islaG Sigma} `{!threadG}
    (sp first second oldra old5 : bv 64) (last : bv 32) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15190 (transactionRecipientOutputPost sp
    (words_20_payload first second last) tail
    (transactionRecipientOutputCallerFrame sp first second last P)) -∗
  instr_body 0x1515c (transactionRecipientCopyEntry sp first second last
    (transactionRecipientCopyBooleanFrame sp oldra old5
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
        (words_20_payload first second last) tail) P)).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_recipient_boolean_output_continuation with "Hcode Hnext") as "#HbooleanNext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_recipient_boolean_call_correct true sp oldra first old5 second
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
      (words_20_payload first second last) tail)
    (transactionRecipientCopiedFrame sp first second last P)
    with "[] Hboolean Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iApply (transactions_recipient_copy_correct with "[]").
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iApply (instr_pre_wand 0x15174 0x15174 false false with "Hcallee"); [done | done |].
  iIntros "Hcopy". iApply (transactions_recipient_copy_to_boolean with "Hcopy HbooleanNext").
Qed.
Print Assumptions transactions_recipient_present_region_correct.
