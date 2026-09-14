Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsBranch WriteSuccessExactTransactionsLiveBranchSpec
  WriteSuccessExactTransactionsLiveNonempty WriteSuccessExactTransactionsLiveComplete.
From IslaTraces.write_success_28 Require Import instrs.

Lemma transactions_live_dispatch_correct `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f08
    (transactionLiveLoopState sp base transactions processed remaining bytes tail P ∗
     ⌜remaining <> []⌝ ∗ True) -∗
  instr_body 0x15668 (transactionLiveLoopExit sp base transactions bytes tail P) -∗
  instr_body 0x14f04
    (transactionLiveLoopState sp base transactions processed remaining bytes tail P).
Proof.
  iStartProof. iIntros "#Hcode Hnext Hexit".
  iAssert (instr_body 0x14f08
    (exactTransactionsBranchState (Z_to_bv 64 (Z.of_nat (length transactions)))
      (Z_to_bv 64 (Z.of_nat (length processed)))
      (transactionLiveBranchFrame sp base transactions processed remaining bytes tail P) ∗
     ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ True))%I
    with "[Hnext]" as "HnextBranch".
  { iApply (instr_pre_wand with "Hnext"); [done | done |].
    iIntros "(Hstate & %Hneq & _)".
    iEval (rewrite -transactions_live_state_branch) in "Hstate".
    iApply (transactions_live_state_nonempty with "Hstate"). done. }
  iAssert (instr_body 0x15668
    (exactTransactionsBranchState (Z_to_bv 64 (Z.of_nat (length transactions)))
      (Z_to_bv 64 (Z.of_nat (length processed)))
      (transactionLiveBranchFrame sp base transactions processed remaining bytes tail P) ∗
     ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ True))%I
    with "[Hexit]" as "HexitBranch".
  { iApply (instr_pre_wand with "Hexit"); [done | done |].
    iIntros "(Hstate & %Heq & _)".
    iEval (rewrite -transactions_live_state_branch) in "Hstate".
    iApply (transactions_live_state_complete with "Hstate"). done. }
  iPoseProof (exact_transactions_branch_correct with "Hcode HnextBranch HexitBranch") as "Hbranch".
  iApply (instr_pre_wand with "Hbranch"); [done | done |].
  iIntros "Hstate". iEval (rewrite transactions_live_state_branch) in "Hstate". iExact "Hstate".
Qed.
Print Assumptions transactions_live_dispatch_correct.
