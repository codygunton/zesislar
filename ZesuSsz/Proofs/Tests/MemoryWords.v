Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryWords.
Require Import isla.riscv64.riscv64.

Lemma memory_word_prefix `{!islaG Sigma} (address : Z) :
  address ↦ₘ? 16 -∗
  ∃ word : bv 64, address ↦ₘ word ∗ (address + 8)%Z ↦ₘ? 8 ∗ True.
Proof. iStartProof. iIntros "Hmemory". zesu_run. Qed.
Print Assumptions memory_word_prefix.

Lemma memory_word_prefix_frame `{!islaG Sigma}
    (address : Z) (P : iProp Sigma) :
  address ↦ₘ? 16 ∗ P -∗
  ∃ word : bv 64, address ↦ₘ word ∗ (address + 8)%Z ↦ₘ? 8 ∗ P ∗ True.
Proof. iStartProof. iIntros "[Hmemory HP]". zesu_run. Qed.
Print Assumptions memory_word_prefix_frame.

Lemma memory_word_six `{!islaG Sigma} (address : Z) :
  address ↦ₘ? 48 -∗ ∃ a b c d e f : bv 64,
  address ↦ₘ a ∗ (address + 8)%Z ↦ₘ b ∗
  (address + 16)%Z ↦ₘ c ∗ (address + 24)%Z ↦ₘ d ∗
  (address + 32)%Z ↦ₘ e ∗ (address + 40)%Z ↦ₘ f ∗ True.
Proof. iStartProof. iIntros "Hmemory". zesu_run. Qed.
Print Assumptions memory_word_six.
