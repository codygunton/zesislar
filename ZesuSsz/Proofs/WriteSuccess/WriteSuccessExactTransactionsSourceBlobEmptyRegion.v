Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsSourceFieldEvents.
From IslaTraces.write_success_65 Require Import instrs.

Lemma transactions_source_blob_empty_correct `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries tail
    (Q : iProp Sigma) :
  transactionRowWord bytes index 232 = BV 64 0 ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15564 (transactionSourceFieldPost sp base bytes processed index
    dataBytes accessBytes chainBytes entries tail Q) -∗
  instr_body 0x153d0 (transactionSourceFieldPost sp base bytes processed index
    dataBytes accessBytes chainBytes entries tail Q).
Proof.
  intros Hzero. iStartProof. iIntros "#Hcode #Hnext".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (instr_lookup_collect _ IslaTraces.write_success_65.instrs.instr_map
    with "Hlookup") as "Hbranch"; first (repeat constructor; reflexivity).
  zesu_block.
Qed.
Print Assumptions transactions_source_blob_empty_correct.
