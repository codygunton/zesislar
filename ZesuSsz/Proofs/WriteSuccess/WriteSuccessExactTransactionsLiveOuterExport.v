Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec
 WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsLiveOuterCode28
 WriteSuccessExactTransactionsLiveStep
 WriteSuccessExactTransactionsOuterClosure.

Lemma transactions_live_complete_outer `{!islaG Sigma} `{!threadG}
 sp base transactions bytes tail (P : iProp Sigma) :
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x15668 (transactionLiveLoopExit sp base transactions bytes tail P) -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
   [] transactions bytes tail P).
Proof.
 iStartProof. iIntros "#Hcode #Hexit".
 iPoseProof (transactions_live_outer_code28 with "Hcode") as "#Hcode28".
 iPoseProof (transactions_live_complete_step sp base transactions bytes tail P
   with "Hcode") as "#Hstep".
 iPoseProof (transactions_live_outer_closure sp base transactions bytes tail P
   with "Hcode28 Hstep Hexit") as "Houter".
 iApply ("Houter" $! [] transactions).
Qed.
Print Assumptions transactions_live_complete_outer.
