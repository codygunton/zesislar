Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsSignatureVRS.

Lemma transactions_signature_complete_code `{!islaG Sigma} `{!threadG}
    sp value r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 old11 tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15620
    (transactionSignatureVRSEntry sp value r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 old11 tail P).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (transactions_signature_vrs_correct with "[] [] [] Hint Hu256 Houtput").
  all: iApply instr_lookup_collect; last iExact "Hlookup".
  all: repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_signature_complete_code.
