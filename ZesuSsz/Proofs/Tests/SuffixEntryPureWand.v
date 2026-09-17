Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Lemma suffix_entry_pure_wand_fixture
    `{!islaG Sigma}
    (P : iProp Sigma) (sp pointer : bv 64) (base : Z)
    (processed remaining : nat) (bytes : list (bv 8)) :
  P -∗
  ((⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜S remaining < 2 ^ 64⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(0 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 1896 < 1073741824)%Z⌝ ∗
    ⌜(0 <= base)%Z⌝ ∗
    ⌜(base + Z.of_nat (length bytes) < 1073741824)%Z⌝ ∗ True) -∗ P).
Proof.
  iStartProof. iIntros "HP". zesu_run.
Qed.

Print Assumptions suffix_entry_pure_wand_fixture.
