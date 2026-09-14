Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma transactions_authorization_scratch `{!islaG Sigma} (sp : Z) :
  0x20000000 <= sp - 48 ->
  sp + 1896 < 0x40000000 ->
  (sp + 1744) ↦ₘ? 40 -∗ (sp + 1784) ↦ₘ? 112 -∗
  (sp + 1744) ↦ₘ? 144 ∗ (sp + 1888) ↦ₘ? 8 ∗ True.
Proof.
  intros Hlow Hhigh. iStartProof. iIntros "Hfirst Hsecond".
  iAssert (∃ _ : unit, (sp + 1744) ↦ₘ? 144 ∗
    (sp + 1888) ↦ₘ? 8 ∗ True)%I with "[Hfirst Hsecond]" as "Hscratch".
  { zesu_run. }
  iDestruct "Hscratch" as (_) "Hscratch". iExact "Hscratch".
Qed.
Print Assumptions transactions_authorization_scratch.
