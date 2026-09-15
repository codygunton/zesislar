Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveFacts
 WriteSuccessExactTransactionsLiveCurrentRowFacts
 WriteSuccessExactTransactionsLiveNonemptyCountHandoff
 WriteSuccessExactTransactionsLiveNonemptyFieldHandoff
 WriteSuccessExactTransactionsLiveZeroFieldToLoop.

Lemma transactions_live_complete_iteration_nonempty `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail row authRest (P : iProp Sigma) :
 writeSuccessTransactionAuthorizations transaction = row :: authRest ->
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
 destruct (transactions_live_current_row_facts sp base transactions processed
   transaction rest bytes Hfacts Hall) as (Hprocessed & Hvalid & _ & _ & _).
 iDestruct (transactions_live_nonempty_count_handoff sp base transactions
   processed transaction rest bytes tail row authRest P Hrows Hfacts Hall
   with "Hcode Hnext Hstate") as "(Hstate & #Hcount)".
 iPoseProof (transactions_live_nonempty_field_handoff sp base transactions
   processed transaction rest bytes tail row authRest P Hrows Hfacts Hall
   with "Hcode Hcount") as "#Hfield".
 iPoseProof (transactions_live_zero_field_to_loop sp base transactions processed
   transaction rest bytes tail P Hfacts Hprocessed Hvalid with "Hcode Hfield") as "Hbody".
 iEval (rewrite instr_pre'_eq) in "Hbody".
 iApply "Hbody". iExact "Hstate".
Qed.
Print Assumptions transactions_live_complete_iteration_nonempty.
