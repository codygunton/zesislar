Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec
 WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsLiveZeroBody
 WriteSuccessExactTransactionsLiveNonemptyBody.

Lemma transactions_live_complete_step `{!islaG Sigma} `{!threadG}
 sp base transactions bytes tail (P : iProp Sigma) :
 writeSuccessCompleteNativeCode -∗
 □ (∀ processed transaction rest,
   □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
     (processed ++ [transaction]) rest bytes tail P) -∗
   instr_body 0x14f08 (transactionLiveLoopState sp base transactions
     processed (transaction :: rest) bytes tail P)).
Proof.
 iIntros "#Hcode". iModIntro.
 iIntros (processed transaction rest) "#Hnext".
 destruct (writeSuccessTransactionAuthorizations transaction)
   as [|row authRest] eqn:Hrows.
 - iApply (transactions_live_complete_iteration_zero sp base transactions
     processed transaction rest bytes tail P Hrows with "Hcode Hnext").
 - iApply (transactions_live_complete_iteration_nonempty sp base transactions
     processed transaction rest bytes tail row authRest P Hrows with "Hcode Hnext").
Qed.
Print Assumptions transactions_live_complete_step.
