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

Lemma test_byte_array_16_uninit_subsumption `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (upper : bv 64) :
  length bytes = 16%nat ->
  0 <= base ->
  base + 32 < 2 ^ 64 ->
  (base + 16) ↦ₘ? 8 -∗ (base + 24) ↦ₘ upper -∗
  subsume (base ↦ₘ∗ bytes) (fun _ : unit => base ↦ₘ? 32)
    (fun _ => True%I).
Proof.
  intros Hlength Hbase Hbound. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try lia.
Qed.

Print Assumptions test_byte_array_16_uninit_subsumption.

Lemma test_byte_array_32_uninit_subsumption `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (upper : bv 64) :
  length bytes = 32%nat ->
  0 <= base ->
  base + 48 < 2 ^ 64 ->
  (base + 32) ↦ₘ? 8 -∗ (base + 40) ↦ₘ upper -∗
  subsume (base ↦ₘ∗ bytes) (fun _ : unit => base ↦ₘ? 48)
    (fun _ => True%I).
Proof.
  intros Hlength Hbase Hbound. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try lia.
Qed.

Print Assumptions test_byte_array_32_uninit_subsumption.

Lemma test_two_words_byte_array_conversion `{!islaG Sigma}
    (base : Z) (low high : bv 64) :
  base ↦ₘ low -∗ (base + 8) ↦ₘ high -∗
  base ↦ₘ∗
      (bv_to_little_endian 8 8 (bv_unsigned low) ++
       bv_to_little_endian 8 8 (bv_unsigned high)).
Proof.
  iStartProof. iIntros "Hlow Hhigh".
  iApply (mem_mapsto_u64_pair_to_byte_array with "Hlow Hhigh").
Qed.

Print Assumptions test_two_words_byte_array_conversion.

Lemma test_four_words_byte_array_conversion `{!islaG Sigma}
    (base : Z) (w0 w1 w2 w3 : bv 64) :
  base ↦ₘ w0 -∗ (base + 8) ↦ₘ w1 -∗
  (base + 16) ↦ₘ w2 -∗ (base + 24) ↦ₘ w3 -∗
  base ↦ₘ∗
    ((bv_to_little_endian 8 8 (bv_unsigned w0) ++
      bv_to_little_endian 8 8 (bv_unsigned w1)) ++
     (bv_to_little_endian 8 8 (bv_unsigned w2) ++
      bv_to_little_endian 8 8 (bv_unsigned w3))).
Proof.
  iStartProof. iIntros "H0 H1 H2 H3".
  iApply (mem_mapsto_u64_quad_to_byte_array with "H0 H1 H2 H3").
Qed.

Print Assumptions test_four_words_byte_array_conversion.
