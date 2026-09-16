Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsValueToData
  WriteSuccessExactTransactionsValueCall WriteSuccessExactTransactionsDataBytesCall
  WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_value_data_continuation `{!islaG Sigma} `{!threadG}
    (data size sp w0 w1 w2 w3 old6 old9 : bv 64) bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size bytes tail))
    (transactionValueDataCaller data size sp w0 w1 w2 w3 old6 old9 bytes tail P)).
Proof.
  iIntros "#Hcode".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_data_bytes_call_correct data size sp (BV 64 0x151b4)
    (sp - BV 64 48)%bv (BV 64 32) (BV 64 (mapIoContextAddress defaultMap)) old6 old9 bytes tail
    (transactionValueDataSourceFrame sp w0 w1 w2 w3 P)
    with "[] Hbytes Hint Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iModIntro. iApply (instr_pre_wand 0x151b4 0x151b4 false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_value_to_data with "Hpost").
Qed.
Print Assumptions transactions_value_data_continuation.
