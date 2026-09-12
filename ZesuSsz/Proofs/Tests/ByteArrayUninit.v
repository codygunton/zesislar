Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Lemma test_byte_array_8_uninit_subsumption `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (upper : bv 64) :
  length bytes = 8%nat ->
  0 <= base ->
  base + 16 <= 2 ^ 64 ->
  (base + 8) ↦ₘ upper -∗
  subsume (base ↦ₘ∗ bytes) (fun _ : unit => base ↦ₘ? 16)
    (fun _ => True%I).
Proof.
  intros Hlength Hbase Hbound. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try lia.
Qed.

Print Assumptions test_byte_array_8_uninit_subsumption.

Lemma test_word_byte_array_subsumption `{!islaG Sigma}
    (base : Z) (byte : bv 8) :
  base ↦ₘ byte -∗
  subsume (base ↦ₘ byte)
    (fun _ : unit => base ↦ₘ∗ [byte]) (fun _ => True%I).
Proof.
  iStartProof. iIntros "Hbyte". liARun.
  Unshelve. all: prepare_sidecond; try reflexivity; try iFrame.
Qed.

Print Assumptions test_word_byte_array_subsumption.
