Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAuthorizationsPrefix.
Lemma transactions_fee_count_complete_code `{!islaG Sigma} `{!threadG}
    sp low high count oldra old5 tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15564 (authorizationPrefixEntry sp low high count oldra old5 tail P).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (authorization_prefix_correct with "[] [] Hu128 Hint Houtput").
  all: iApply instr_lookup_collect; last iExact "Hlookup".
  all: repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_fee_count_complete_code.
