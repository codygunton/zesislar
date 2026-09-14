Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAuthorizationsCompleteCode
  WriteSuccessExactAuthorizationsCountContinuation WriteSuccessExactAuthorizationsCountInitial
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactAuthorizationsModel.

Lemma authorization_complete_count_continuation `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) base row rest source tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (writeSuccessExactAuthorizationEvents sp (row :: rest) tail)
    (maxBlobFeeCountFrame sp low high (authorizationInitialCaller sp low high base row rest source tail P))).
Proof.
  iStartProof. iIntros "#Hcode".
  iPoseProof (authorization_complete_loop_code with "Hcode") as "#Hloop".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (authorization_count_continuation_closed with "[] Hloop").
  iApply instr_lookup_collect; last iExact "Hlookup".
  repeat constructor; reflexivity.
Qed.
Print Assumptions authorization_complete_count_continuation.
