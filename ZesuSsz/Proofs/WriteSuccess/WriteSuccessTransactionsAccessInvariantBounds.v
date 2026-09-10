Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Lemma write_success_transactions_access_invariant_bounds
    `{!islaG Sigma} (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (R : iProp Sigma)
    (HbaseLow : 0x20000000 <= base)
    (HbaseHigh : base + Z.of_nat (length bytes) < 0x40000000) :
  R -∗
  ⌜entries <> [] -> 0x20000000 <= base⌝ ∗
  ⌜entries <> [] -> base + Z.of_nat (length bytes) < 0x40000000⌝ ∗ R.
Proof.
  iIntros "HR".
  iSplit; [iPureIntro; intros _; exact HbaseLow|].
  iSplit; [iPureIntro; intros _; exact HbaseHigh|].
  iExact "HR".
Qed.
