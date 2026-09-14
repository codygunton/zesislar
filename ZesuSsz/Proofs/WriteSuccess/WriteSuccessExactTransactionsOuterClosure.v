Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLiveDispatch.
From IslaTraces.write_success_28 Require Import instrs.

Lemma transactions_live_outer_closure `{!islaG Sigma} `{!threadG}
    sp base transactions bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ (∀ processed transaction rest,
    □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
      (processed ++ [transaction]) rest bytes tail P) -∗
    instr_body 0x14f08 (transactionLiveLoopState sp base transactions
      processed (transaction :: rest) bytes tail P)) -∗
  □ instr_pre 0x15668 (transactionLiveLoopExit sp base transactions bytes tail P) -∗
  ∀ processed remaining,
    □ instr_pre 0x14f04
      (transactionLiveLoopState sp base transactions processed remaining bytes tail P).
Proof.
  iStartProof. iIntros "#Hcode #Hstep #Hexit" (processed remaining).
  iLöb as "IH" forall (processed remaining).
  iModIntro. iApply instr_pre_to_body.
  iEval (rewrite instr_pre'_eq) in "Hexit".
  iNext.
  iAssert (instr_body 0x14f08
    (transactionLiveLoopState sp base transactions processed remaining bytes tail P ∗
     ⌜remaining <> []⌝ ∗ True))%I with "[]" as "Hnonempty".
  { destruct remaining as [|transaction rest].
    - rewrite instr_pre'_eq. iIntros "(_ & %Hfalse & _)". done.
    - iPoseProof ("Hstep" $! processed transaction rest with "[]") as "Hbody".
      { iApply ("IH" $! (processed ++ [transaction]) rest). }
      iApply (instr_pre_wand with "Hbody"); [done | done |].
      iIntros "(Hstate & _ & _)". iExact "Hstate". }
  iApply (transactions_live_dispatch_correct with "Hcode Hnonempty [Hexit]").
  iEval (rewrite instr_pre'_eq). iExact "Hexit".
Qed.
Print Assumptions transactions_live_outer_closure.
