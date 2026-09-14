Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.UninitRegions.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessTransactionsSpec.

Lemma transaction_cursor_region_test `{!islaG Sigma} `{!threadG}
    (sp : bv 64) transactions (P : iProp Sigma) :
  ⌜bv_unsigned sp + 1896 < 0x28000000⌝ -∗
  ⌜Forall writeSuccessTransactionValid transactions⌝ -∗
  (bv_unsigned sp - 48) ↦ₘ? 48 -∗
  (bv_unsigned sp + 120) ↦ₘ? 160 -∗
  (bv_unsigned sp + 1640) ↦ₘ? 256 -∗ P -∗
  (bv_unsigned sp + 248) ↦ₘ? 8 ∗
  (bv_unsigned sp + 120) ↦ₘ? 128 ∗
  (bv_unsigned sp + 256) ↦ₘ? 24 ∗
  (bv_unsigned sp - 48) ↦ₘ? 48 ∗
  (bv_unsigned sp + 1640) ↦ₘ? 256 ∗ P ∗ True.
Proof.
  iStartProof. iIntros "%Hbound %Hvalid Hnegative Hscratch Hsource HP".
  iAssert (∃ _ : unit,
    (bv_unsigned sp + 248) ↦ₘ? 8 ∗
    (bv_unsigned sp + 120) ↦ₘ? 128 ∗
    (bv_unsigned sp + 256) ↦ₘ? 24 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 1640) ↦ₘ? 256 ∗ P ∗ True)%I
    with "[Hnegative Hscratch Hsource HP]" as "Hresult".
  { zesu_run. }
  iDestruct "Hresult" as (_) "Hresult". iExact "Hresult".
Qed.
Print Assumptions transaction_cursor_region_test.
