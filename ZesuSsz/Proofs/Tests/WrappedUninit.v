Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
Open Scope Z_scope.
Lemma root_memcpy_scratch_borrow_return `{!islaG Sigma} `{!threadG} (sp : bv 64) :
  2176 <= bv_unsigned sp ->
  (bv_unsigned sp - 2000) ↦ₘ? 1896 -∗
  bv_unsigned (sp + BV 64 18446744073709549616 + BV 64 312)%bv ↦ₘ? 720 ∗
  (bv_unsigned (sp + BV 64 18446744073709549616 + BV 64 312)%bv ↦ₘ? 720 -∗
   (bv_unsigned sp - 2000) ↦ₘ? 1896).
Proof.
  intros Hmin.
  iIntros "Hscratch".
  time zesu_open_declared_memory_goal_if_enabled.
  zesu_run.
Qed.
Print Assumptions root_memcpy_scratch_borrow_return.
Lemma wrapped_address_requires_bound `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) :
  (bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P ⊢
  (bv_unsigned (sp + BV 64 18446744073709549616 + BV 64 312)%bv ↦ₘ? 720 ∗ P) ∨
  ((bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P).
Proof using All.
 iIntros "[Hscratch HP]".
 assert_fails (iLeft; zesu_open_declared_memory_goal_if_enabled).
 iRight. iFrame.
Qed.
Section disabled.
Local Remove Hints zesu_switch_sealed_open : typeclass_instances.
Lemma wrapped_address_disabled `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
 (Hmin : 2176 <= bv_unsigned sp) :
  (bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P ⊢
  (bv_unsigned (sp + BV 64 18446744073709549616 + BV 64 312)%bv ↦ₘ? 720 ∗ P) ∨
  ((bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P).
Proof using All.
 iIntros "[Hscratch HP]".
 assert_fails (iLeft; zesu_open_declared_memory_goal_if_enabled).
 iRight. iFrame.
Qed.
End disabled.
Print Assumptions wrapped_address_requires_bound.
Print Assumptions wrapped_address_disabled.
