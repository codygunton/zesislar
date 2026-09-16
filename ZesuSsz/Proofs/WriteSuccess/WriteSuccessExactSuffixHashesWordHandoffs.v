Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesWord3 WriteSuccessExactSuffixHashesWord2
  WriteSuccessExactSuffixHashesWord1 WriteSuccessExactSuffixHashesWord0.

Definition suffixWordFrame3 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (source : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1752) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1760) ↦ₘ? 8 ∗
   ⌜(bv_unsigned sp + 1776 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWordFrame3) := I.

Definition suffixWordFrame2 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (source : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1752) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1768) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 24)%nat source)))) ∗
   ⌜(bv_unsigned sp + 1776 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWordFrame2) := I.

Definition suffixWordFrame1 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (source : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1760) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 16)%nat source)))) ∗
   (bv_unsigned sp + 1768) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 24)%nat source)))) ∗
   ⌜(bv_unsigned sp + 1776 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWordFrame1) := I.

Definition suffixWordFrame0 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (source : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1752) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 8)%nat source)))) ∗
   (bv_unsigned sp + 1760) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 16)%nat source)))) ∗
   (bv_unsigned sp + 1768) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 24)%nat source)))) ∗
   ⌜(bv_unsigned sp + 1776 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWordFrame0) := I.

Lemma suffix_word3_handoff `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  suffixWord3Post sp pointer base source index (suffixWordFrame3 sp source index P) -∗
  suffixWord2Entry sp pointer base source index (suffixWordFrame2 sp source index P).
Proof.
  unfold suffixWord3Post, suffixWord2Entry, suffixWordFrame3, suffixWordFrame2.
  iIntros "(Hsys & Hsp & Hptr & Hregs & Hsource & Hword & %Hcursor & %Hbound & %Hbase & %Hend & %Halign & %Hlow & %Hhigh & Hframe & _)".
  iDestruct "Hframe" as "(H0 & H1 & H2 & %Hwhole & HP & _)".
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions suffix_word3_handoff.

Lemma suffix_word2_handoff `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  suffixWord2Post sp pointer base source index (suffixWordFrame2 sp source index P) -∗
  suffixWord1Entry sp pointer base source index (suffixWordFrame1 sp source index P).
Proof.
  unfold suffixWord2Post, suffixWord1Entry, suffixWordFrame2, suffixWordFrame1.
  iIntros "(Hsys & Hsp & Hptr & Hregs & Hsource & Hword & %Hcursor & %Hbound & %Hbase & %Hend & %Halign & %Hlow & %Hhigh & Hframe & _)".
  iDestruct "Hframe" as "(H0 & H1 & H3 & %Hwhole & HP & _)".
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions suffix_word2_handoff.

Lemma suffix_word1_handoff `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  suffixWord1Post sp pointer base source index (suffixWordFrame1 sp source index P) -∗
  suffixWord0Entry sp pointer base source index (suffixWordFrame0 sp source index P).
Proof.
  unfold suffixWord1Post, suffixWord0Entry, suffixWordFrame1, suffixWordFrame0.
  iIntros "(Hsys & Hsp & Hptr & Hregs & Hsource & Hword & %Hcursor & %Hbound & %Hbase & %Hend & %Halign & %Hlow & %Hhigh & Hframe & _)".
  iDestruct "Hframe" as "(H0 & H2 & H3 & %Hwhole & HP & _)".
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions suffix_word1_handoff.
