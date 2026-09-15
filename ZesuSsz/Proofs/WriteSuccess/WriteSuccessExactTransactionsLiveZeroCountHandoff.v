Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsLiveCurrentRowFacts
 WriteSuccessExactTransactionsLiveAuthorizationCountFacts
 WriteSuccessExactTransactionsLiveSignatureGuard
 WriteSuccessExactTransactionsLiveZeroGuard.

Lemma transactions_live_zero_count_handoff `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
 writeSuccessTransactionAuthorizations transaction = [] ->
 transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
 Forall writeSuccessTransactionValid transactions ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
   (processed ++ [transaction]) rest bytes tail P) -∗
 □ instr_pre 0x15584 (transactionLiveZeroCountEntry sp base transactions
   processed transaction rest bytes tail P).
Proof.
 intros Hrows Hfacts Hall.
 destruct (transactions_live_current_row_facts sp base transactions processed
   transaction rest bytes Hfacts Hall) as (_ & Hvalid & Hrow & _).
 have HfactsCopy := Hfacts.
 destruct HfactsCopy as
  (_ & _ & _ & _ & _ & _ & HstackHigh & _).
 have HauthFacts := transactions_live_authorization_count_facts transaction bytes
   (288 * length processed) Hvalid ltac:(apply Hrow; lia).
 destruct HauthFacts as (HauthCountWord & _ & _).
 have HauthBytes : writeSuccessTransactionAuthorizationBytes transaction = [].
 { unfold writeSuccessTransactionAuthorizationBytes. rewrite Hrows. reflexivity. }
 have HauthCountZero :
   transactionRowWord bytes (288 * length processed) 248 = BV 64 0.
 { rewrite HauthCountWord Hrows. bv_solve. }
 iIntros "#Hcode #Hnext".
 iPoseProof (transactions_live_signature_guard sp base transactions processed
   transaction rest bytes tail P Hfacts with "Hcode Hnext") as "#Hsignature".
 iEval (rewrite HauthBytes) in "Hsignature".
 iApply (transactions_live_zero_count_transition sp base transactions processed
   transaction rest bytes tail P HstackHigh HauthCountZero
   with "Hcode Hsignature").
Qed.
Print Assumptions transactions_live_zero_count_handoff.
