Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments tactics.
Open Scope Z_scope.
Definition borrowedFrameRaw `{!islaG Sigma} (base : Z) : iProp Sigma :=
 (base ↦ₘ? 1896 ∗ (base - 48) ↦ₘ? 48 ∗ (base - 80) ↦ₘ? 32)%I.
Definition borrowedFrame `{!islaG Sigma} (base : Z) : iProp Sigma := borrowedFrameRaw base.
Global Instance borrowedFrame_seal `{!islaG Sigma} base :
 ZesuSealed (borrowedFrame base) (borrowedFrameRaw base)
   [(base, base + 1896)] [] := ltac:(done).
Global Opaque borrowedFrame.
Lemma contained_borrow `{!islaG Sigma} `{!threadG} (base : Z) (P : iProp Sigma)
 (Hbase : (80 <= base)%Z) (Hupper : (base + 1896 < 1073741824)%Z) :
 borrowedFrame base ∗ P ⊢
 (base + 312) ↦ₘ? 720 ∗ base ↦ₘ? 312 ∗ (base + 1032) ↦ₘ? 864 ∗
 (base - 48) ↦ₘ? 48 ∗ (base - 80) ↦ₘ? 32 ∗ P.
Proof using All.
 iIntros "[Hframe HP]".
 time zesu_open_declared_uninit_goal.
 timeout 5 (repeat liAStep).
iAssumption. Unshelve. all: unfold SHELVED_SIDECOND; zesu_region_bounds. Qed.
Print Assumptions contained_borrow.
Lemma wrapped_borrow_range (entrySp : bv 64)
 (Hlower : (2176 <= bv_unsigned entrySp)%Z)
 (Hupper : (bv_unsigned entrySp + 2000 < 1073741824)%Z) :
 (0 <= bv_unsigned (BV 64 720) /\
  bv_unsigned entrySp - 2000 <= bv_unsigned (entrySp + 18446744073709549616 + 312) /\
  bv_unsigned (entrySp + 18446744073709549616 + 312) + bv_unsigned (BV 64 720)
    <= bv_unsigned entrySp - 2000 + 1896)%Z.
Proof using All. time zesu_region_bounds. Qed.
Lemma outside_borrow_rejects `{!islaG Sigma} `{!threadG} (base : Z) (P : iProp Sigma) :
 borrowedFrame base ∗ P ⊢
 ((base + 1800) ↦ₘ? 720 ∗ P) ∨ (borrowedFrame base ∗ P).
Proof using All.
 iIntros "[Hframe HP]".
 assert_fails (iLeft; zesu_open_declared_uninit_goal).
 iRight. iFrame.
Qed.
Print Assumptions wrapped_borrow_range.
Print Assumptions outside_borrow_rejects.
Lemma borrow_after_source `{!islaG Sigma} `{!threadG}
 (base source : Z) (bytes : list (bv 8)) (P : iProp Sigma)
 (Hbase : (80 <= base)%Z) (Hupper : (base + 1896 < 1073741824)%Z) :
 source ↦ₘ∗ bytes ∗ borrowedFrame base ∗ P ⊢
 source ↦ₘ∗ bytes ∗ (base + 312) ↦ₘ? 720 ∗ base ↦ₘ? 312 ∗
 (base + 1032) ↦ₘ? 864 ∗ (base - 48) ↦ₘ? 48 ∗ (base - 80) ↦ₘ? 32 ∗ P.
Proof using All.
 iIntros "[Hsource [Hframe HP]]".
 time zesu_open_declared_uninit_goal.
 iFrame "Hsource".
 timeout 5 (repeat liAStep).
 iAssumption. Unshelve. all: unfold SHELVED_SIDECOND; zesu_region_bounds.
Qed.
Print Assumptions borrow_after_source.
