Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma test_explicit_large_byte_array_uninit `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 64%nat ->
  (base + 64) ↦ₘ? 8 -∗
  subsume (base ↦ₘ∗ bytes) (fun _ : unit => base ↦ₘ? 72)
    (fun _ => True%I).
Proof.
  intros Hlength. iStartProof. iIntros "Htail".
  iApply subsume_mem_byte_array_uninit.
  rewrite Hlength /=. iFrame.
  repeat iSplit; done.
Qed.

Print Assumptions test_explicit_large_byte_array_uninit.
