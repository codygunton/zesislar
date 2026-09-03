From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_74 Require Import a1558c.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.

Definition writeSuccessTransactionsAt1558cZeroLeafSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   P ∗
   instr_pre 0x15620
     (reg_col zesu_ram_sys_regs ∗
      "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cZeroLeafSpec) := I.

Definition writeSuccessTransactionsAt1558cNonzeroLeafSpec
    `{!islaG Sigma} `{!threadG} (count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits count ∗
   P ∗
   instr_pre 0x15590
     (reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits count ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cNonzeroLeafSpec) := I.

Definition writeSuccessTransactionsAt1558cBranchLeafSpec
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) : iProp Sigma :=
  (writeSuccessTransactionsAt1558cZeroLeafSpec (P (BV 64 0)) ∨
   ∃ count : bv 64, ⌜count <> BV 64 0⌝ ∗
     writeSuccessTransactionsAt1558cNonzeroLeafSpec count (P count))%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cBranchLeafSpec) := I.

Lemma write_success_transactions_chunk_1558c_zero_leaf
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x1558c (Some a1558c) -∗
  instr_body 0x1558c (writeSuccessTransactionsAt1558cZeroLeafSpec P).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  Unshelve. all: try iFrame.
  all: lazymatch goal with |- ?G => fail "branch1558c zero leaf" G end.
Qed.

Lemma write_success_transactions_chunk_1558c_nonzero_leaf
    `{!islaG Sigma} `{!threadG} (count : bv 64)
    (Hcount : count <> BV 64 0) (P : iProp Sigma) :
  instr 0x1558c (Some a1558c) -∗
  instr_body 0x1558c
    (writeSuccessTransactionsAt1558cNonzeroLeafSpec count P).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try match goal with
  | |- _ => exfalso; apply Hcount; bv_solve
  end.
  all: try bv_solve.
  Unshelve. all: try iFrame.
  all: try (iExFalso; iPureIntro; apply Hcount; bv_solve).
  all: lazymatch goal with |- ?G => fail "branch1558c nonzero leaf" G end.
Qed.

Lemma write_success_transactions_chunk_1558c_branch_leaf
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr 0x1558c (Some a1558c) -∗
  instr_body 0x1558c (writeSuccessTransactionsAt1558cBranchLeafSpec P).
Proof.
  iStartProof.
  iIntros "#Hbranch".
  iApply (instr_pre_intro_Some with "Hbranch").
  iIntros "[Hzero | Hnonzero] HPC".
  - iEval (rewrite /writeSuccessTransactionsAt1558cZeroLeafSpec) in "Hzero".
    iDestruct "Hzero" as "(Hsys & H18 & HP & Hdest & _)".
    liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption.
    all: try bv_solve.
    Unshelve. all: try iFrame.
    all: lazymatch goal with |- ?G => fail "combined zero leaf" G end.
  - iDestruct "Hnonzero" as (count Hcount) "Hnonzero".
    iEval (rewrite /writeSuccessTransactionsAt1558cNonzeroLeafSpec)
      in "Hnonzero".
    iDestruct "Hnonzero" as "(Hsys & H18 & HP & Hdest & _)".
    liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption.
    all: try close_infeasible_bv_branches.
    all: try bv_solve.
    Unshelve. all: try iFrame.
    all: try (iExFalso; iPureIntro; apply Hcount; bv_solve).
    all: lazymatch goal with |- ?G => fail "combined nonzero leaf" G end.
Qed.
