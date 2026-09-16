Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactBlobHashesNativeEntry
  WriteSuccessExactBlobHashesHeader.
From IslaTraces.write_success_blocks Require Import Index.

Lemma blob_complete_native_entry_correct `{!islaG Sigma} `{!threadG}
    sp pointer base total bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x153d0 (blobHeaderEntry sp pointer base total bytes tail P).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (blob_native_entry_correct with "[] [] [] [] [] [] [] Houtput").
  all: iApply instr_lookup_collect; last iExact "Hlookup".
  all: repeat constructor; reflexivity.
Qed.
Print Assumptions blob_complete_native_entry_correct.
