Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.

Lemma words_20_source_array_frame `{!islaG Sigma}
    (a source : Z) (first second : bv 64) (last : bv 32)
    (bytes : list (bv 8)) :
  (a ↦ₘ first ∗ (a + 8) ↦ₘ second ∗ (a + 16) ↦ₘ last ∗
   source ↦ₘ∗ bytes ∗ True)%I -∗
  (a ↦ₘ∗ words_20_payload first second last ∗ source ↦ₘ∗ bytes ∗ True)%I.
Proof.
  iIntros "(Hfirst & Hsecond & Hlast & Hsource & _)".
  iFrame "Hsource". iApply words_20_payload_merge. iFrame.
Qed.
Print Assumptions words_20_source_array_frame.
