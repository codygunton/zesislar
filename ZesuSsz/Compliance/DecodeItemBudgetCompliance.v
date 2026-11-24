(* The charged decodeItem contract (plan Stage T, T7): every run from the entry
   to the return fetches at most decodeItemBudget (75) instructions of the
   function, with the outcome relation of decodeItemSelectedModel. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemChargedSelected.
Require Import ZesuSsz.Contracts.DecodeItemBudgetContract.
Require Import ZesuSsz.Compliance.DecodeItemBudgetComposition.
Local Open Scope Z_scope.

Theorem decodeItemBudgetCompliance : DecodeItemBudgetContractCorrect.
Proof.
  intros returnAddress Sigma HG HT.
  exact (@fp301b_budget_body Sigma HG HT returnAddress).
Qed.

Print Assumptions decodeItemBudgetCompliance.
