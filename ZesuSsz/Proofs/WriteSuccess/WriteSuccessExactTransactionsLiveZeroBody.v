Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveFacts
 WriteSuccessExactTransactionsLiveCurrentRowFacts
 WriteSuccessExactTransactionsLiveZeroCountHandoff
 WriteSuccessExactTransactionsLiveZeroFieldHandoff
 WriteSuccessExactTransactionsLiveZeroFieldToLoop.

Lemma transactions_live_complete_iteration_zero `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
 writeSuccessTransactionAuthorizations transaction = [] ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
   (processed ++ [transaction]) rest bytes tail P) -∗
 instr_body 0x14f08 (transactionLiveLoopState sp base transactions
   processed (transaction :: rest) bytes tail P).
Proof.
 intros Hrows.
 iStartProof. iIntros "#Hcode #Hnext".
 iEval (rewrite instr_pre'_eq). iIntros "Hstate".
 iDestruct (transactions_live_state_facts with "Hstate")
   as "(Hstate & %Hall & %Hfacts & _)".
 have HrowFacts := transactions_live_current_row_facts sp base transactions
   processed transaction rest bytes Hfacts Hall.
 destruct HrowFacts as (Hprocessed & Hvalid & _ & _ & _).
 iPoseProof (transactions_live_zero_count_handoff sp base transactions processed
   transaction rest bytes tail P Hrows Hfacts Hall with "Hcode Hnext") as "#Hcount".
 iPoseProof (transactions_live_zero_field_handoff sp base transactions processed
   transaction rest bytes tail P Hrows Hfacts Hall with "Hcode Hcount") as "#Hfield".
 iPoseProof (transactions_live_zero_field_to_loop sp base transactions processed
   transaction rest bytes tail P Hfacts Hprocessed Hvalid with "Hcode Hfield") as "Hbody".
 iEval (rewrite instr_pre'_eq) in "Hbody".
 iApply "Hbody". iExact "Hstate".
Qed.
Print Assumptions transactions_live_complete_iteration_zero.
