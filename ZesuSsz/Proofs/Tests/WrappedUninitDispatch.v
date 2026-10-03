Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
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
  zesu_block.
Qed.
Print Assumptions root_memcpy_scratch_borrow_return.
Section disabled.
Local Remove Hints zesu_switch_sealed_open : typeclass_instances.
Lemma wrapped_dispatch_disabled `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
 (Hmin : (2176 <= bv_unsigned sp)%Z) :
 (bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P ⊢
 (bv_unsigned (sp + BV 64 18446744073709549616 + BV 64 312)%bv ↦ₘ? 720 ∗ P) ∨
 ((bv_unsigned sp - 2000) ↦ₘ? 1896 ∗ P).
Proof using All.
 iIntros "[Hscratch HP]".
 assert_fails (iLeft; zesu_normalize_uninit_wrapped_address_if_enabled).
 assert_fails (iLeft; solve [zesu_block]).
 iRight. iFrame.
Qed.
End disabled.
Print Assumptions wrapped_dispatch_disabled.
