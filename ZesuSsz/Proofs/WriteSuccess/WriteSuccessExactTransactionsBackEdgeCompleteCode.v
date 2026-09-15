Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeCode WriteSuccessExactTransactionsBackEdge.
Lemma transactions_back_edge_complete_code `{!islaG Sigma} `{!threadG}
 sp index total (P : iProp Sigma) :
 writeSuccessCompleteNativeCode -∗
 instr_body 0x1565c (transactionBackEdgeEntry sp index total P).
Proof.
 iIntros "#Hcode".
 iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
 iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
 iPoseProof (instr_lookup_collect IslaTraces.write_success_blocks.Index.lookup [(0x14f00, IslaTraces.write_success_28.a14f00.a14f00)]
  ltac:(repeat constructor; reflexivity) with "Hlookup") as "#Hsingle".
 iEval (rewrite big_sepL_cons big_sepL_nil) in "Hsingle".
 iDestruct "Hsingle" as "[#Hindex _]".
 iApply (transactions_back_edge_correct with "[] Hindex").
 iApply instr_lookup_collect; last iExact "Hlookup".
 repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_back_edge_complete_code.
