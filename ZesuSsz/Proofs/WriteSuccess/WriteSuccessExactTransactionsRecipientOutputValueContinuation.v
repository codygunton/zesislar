Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientOutputToValue
  WriteSuccessExactTransactionsRecipientBooleanToOutput WriteSuccessExactTransactionsRecipientOutput
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_47 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma transactions_recipient_output_value_continuation `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 old13 : bv 64) (last : bv 32)
    tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientValueSourceFrame sp first second last P)) -∗
  □ instr_pre 0x15190 (transactionRecipientOutputPost sp (words_20_payload first second last)
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)
    (transactionRecipientOutputCallerFrame sp first second last
      (transactionRecipientValuePreparation sp w0 w1 w2 w3 old13 P))).
Proof.
  iIntros "#Hcode #Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_value_call_correct sp w0 w1 w2 w3 (BV 64 0x15190)
    (BV 64 (mapIoContextAddress defaultMap)) tail (transactionRecipientValueSourceFrame sp first second last P)
    with "[] Hu256 Houtput") as "Hvalue".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_47.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hjoin".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iAssert (instr_body 0x15190 (transactionValueEntry sp w0 w1 w2 w3
    (BV 64 0x15190) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionRecipientValueSourceFrame sp first second last P)))%I
    with "[Hvalue]" as "Hcallee".
  { iEval (rewrite /IslaTraces.write_success_47.instrs.instr_map /=) in "Hjoin".
    iDestruct "Hjoin" as "#(Hjump & _)". zesu_run. }
  iModIntro. iApply (instr_pre_wand 0x15190 0x15190 false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_recipient_output_to_value with "Hpost Hnext").
Qed.
Print Assumptions transactions_recipient_output_value_continuation.
