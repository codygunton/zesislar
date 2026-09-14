Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordArrays.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma transaction_byte_array_own_view `{!islaG Sigma} pointer bytes :
  writeSuccessByteArrayOwn pointer bytes ⊣⊢
  bv_unsigned pointer ↦ₘ∗ bytes ∗
  ⌜bytes <> [] -> 0x20000000 <= bv_unsigned pointer /\
    bv_unsigned pointer + Z.of_nat (length bytes) < 0x40000000⌝ ∗ True.
Proof.
  destruct bytes as [|byte bytes]; cbn [writeSuccessByteArrayOwn].
  - iSplit.
    + iIntros "_". iSplitL.
      * iApply byte_array_empty. iPureIntro. bv_solve.
      * iSplit; [iPureIntro; intros Hnonempty; contradiction | done].
    + iIntros "_". done.
  - iSplit.
    + iIntros "(Hbytes & %Hlow & %Hhigh & _)". iFrame.
      iSplit; [iPureIntro; intros _; split; assumption | done].
    + iIntros "(Hbytes & %Hbounds & _)".
      destruct (Hbounds ltac:(discriminate)) as [Hlow Hhigh]. iFrame. done.
Qed.
Print Assumptions transaction_byte_array_own_view.
