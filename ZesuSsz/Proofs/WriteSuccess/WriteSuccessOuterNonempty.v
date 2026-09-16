Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_28 Require Import a14f04.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessOuterNonemptyState
    `{!islaG Sigma} `{!threadG} (R : iProp Sigma)
    (index total : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits total ∗ "x11" ↦ᵣ RVal_Bits index ∗ R)%I.

Lemma write_success_outer_nonempty_branch
    `{!islaG Sigma} `{!threadG} (R : iProp Sigma)
    (index total : bv 64) (Hnonempty : index ≠ total) :
  instr 0x14f04 (Some IslaTraces.write_success_28.a14f04.a14f04) -∗
  instr_pre 0x14f08 (writeSuccessOuterNonemptyState R index total) -∗
  instr_body 0x14f04 (writeSuccessOuterNonemptyState R index total).
Proof.
  iStartProof.
  iIntros "Hinstr Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold writeSuccessOuterNonemptyState) in "Hentry".
  iDestruct "Hentry" as "(Hsys & H10 & H11 & HR)".
  iExists (Some IslaTraces.write_success_28.a14f04.a14f04).
  iSplitL "Hinstr"; first iExact "Hinstr".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try (exfalso; apply Hnonempty; bv_solve).
  all: try (exfalso; apply Hnonempty; reflexivity).
  all: try congruence.
  all: try iFrame.
  all: try (rewrite /writeSuccessOuterNonemptyState; iFrame).
  Unshelve. all: rewrite /writeSuccessOuterNonemptyState; iFrame.
  Unshelve. all: exfalso; apply Hnonempty; reflexivity.
Qed.
