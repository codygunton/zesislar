Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_38 Require Import a15118.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessTransactions15118BranchState
    `{!islaG Sigma} `{!threadG} (R : iProp Sigma) (data : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x27" ↦ᵣ RVal_Bits data ∗ R)%I.

Lemma write_success_transactions_15118_zero_branch
    `{!islaG Sigma} `{!threadG} (R : iProp Sigma) (data : bv 64)
    (Hzero : data = BV 64 0) :
  instr 0x15118 (Some IslaTraces.write_success_38.a15118.a15118) -∗
  instr_pre 0x1513c (writeSuccessTransactions15118BranchState R data) -∗
  instr_body 0x15118 (writeSuccessTransactions15118BranchState R data).
Proof.
  subst data. iStartProof.
  iIntros "Hinstr Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold writeSuccessTransactions15118BranchState) in "Hentry".
  iDestruct "Hentry" as "(Hsys & H27 & HR)".
  iExists (Some IslaTraces.write_success_38.a15118.a15118).
  iSplitL "Hinstr"; first iExact "Hinstr".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try iFrame.
  all: try (rewrite /writeSuccessTransactions15118BranchState; iFrame).
  Unshelve. all: rewrite /writeSuccessTransactions15118BranchState; iFrame.
Qed.

Lemma write_success_transactions_15118_nonzero_branch
    `{!islaG Sigma} `{!threadG} (R : iProp Sigma) (data : bv 64)
    (Hnonzero : data ≠ BV 64 0) :
  instr 0x15118 (Some IslaTraces.write_success_38.a15118.a15118) -∗
  instr_pre 0x1511c (writeSuccessTransactions15118BranchState R data) -∗
  instr_body 0x15118 (writeSuccessTransactions15118BranchState R data).
Proof.
  iStartProof.
  iIntros "Hinstr Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold writeSuccessTransactions15118BranchState) in "Hentry".
  iDestruct "Hentry" as "(Hsys & H27 & HR)".
  iExists (Some IslaTraces.write_success_38.a15118.a15118).
  iSplitL "Hinstr"; first iExact "Hinstr".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try (exfalso; apply Hnonzero; bv_solve).
  all: try (exfalso; apply Hnonzero; reflexivity).
  all: try congruence.
  all: try iFrame.
  all: try (rewrite /writeSuccessTransactions15118BranchState; iFrame).
  Unshelve. all: rewrite /writeSuccessTransactions15118BranchState; iFrame.
  Unshelve. all: exfalso; apply Hnonzero; reflexivity.
Qed.
