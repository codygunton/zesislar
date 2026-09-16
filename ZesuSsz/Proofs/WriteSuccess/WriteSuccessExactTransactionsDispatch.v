Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsResources.
From IslaTraces.write_success_28 Require Import instrs.
Import ListNotations.

Lemma write_success_exact_transactions_dispatch `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f08
    (writeSuccessExactTransactionsState sp base transactions processed remaining
      bytes tail P ∗ ⌜remaining <> []⌝ ∗ True) -∗
  instr_body 0x15668
    (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) -∗
  instr_body 0x14f04
    (writeSuccessExactTransactionsState sp base transactions processed remaining
      bytes tail P).
Proof.
  iStartProof. iIntros "#Hcode Hnext Hexit".
  iAssert (instr_body 0x14f08
    (exactTransactionsBranchState
      (Z_to_bv 64 (Z.of_nat (length transactions)))
      (Z_to_bv 64 (Z.of_nat (length processed)))
      (writeSuccessExactTransactionsBranchFrame sp base transactions processed
        remaining bytes tail P) ∗
      ⌜Z_to_bv 64 (Z.of_nat (length processed)) <>
        Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ True))%I
    with "[Hnext]" as "HnextBranch".
  { iApply (instr_pre_wand with "Hnext"); [done | done |].
    iIntros "(Hstate & %Hneq & _)".
    iEval (rewrite -writeSuccessExactTransactionsState_branch) in "Hstate".
    iApply (writeSuccessExactTransactionsState_nonempty with "Hstate"). done. }
  iAssert (instr_body 0x15668
    (exactTransactionsBranchState
      (Z_to_bv 64 (Z.of_nat (length transactions)))
      (Z_to_bv 64 (Z.of_nat (length processed)))
      (writeSuccessExactTransactionsBranchFrame sp base transactions processed
        remaining bytes tail P) ∗
      ⌜Z_to_bv 64 (Z.of_nat (length processed)) =
        Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ True))%I
    with "[Hexit]" as "HexitBranch".
  { iApply (instr_pre_wand with "Hexit"); [done | done |].
    iIntros "(Hstate & %Heq & _)".
    iEval (rewrite -writeSuccessExactTransactionsState_branch) in "Hstate".
    iApply (writeSuccessExactTransactionsState_complete with "Hstate"). done. }
  iPoseProof (exact_transactions_branch_correct with
    "Hcode HnextBranch HexitBranch") as "Hbranch".
  iApply (instr_pre_wand with "Hbranch"); [done | done |].
  iIntros "Hstate".
  iEval (rewrite writeSuccessExactTransactionsState_branch) in "Hstate".
  iExact "Hstate".
Qed.
Print Assumptions write_success_exact_transactions_dispatch.
