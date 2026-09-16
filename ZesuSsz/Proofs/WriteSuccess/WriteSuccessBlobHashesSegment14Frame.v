Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Lemma write_success_blob_hashes_segment14_raw_frame
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed remaining : nat)
    (bytes : list (bv 8)) :
  base ↦ₘ∗ take (32 * processed + 8) bytes -∗
  (base + Z.of_nat (32 * processed + 9)) ↦ₘ∗
    drop (32 * processed + 9) bytes -∗
  ⌜length bytes = (32 * (processed + S remaining))%nat⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  let byte := default (BV 8 0) (bytes !! (32 * processed + 8)%nat) in
  base ↦ₘ∗ take (32 * processed) bytes ∗
  bv_unsigned pointer ↦ₘ∗ take 8 (drop (32 * processed) bytes) ∗
  (bv_unsigned pointer + 9) ↦ₘ∗ drop 9 (drop (32 * processed) bytes).
Proof.
  iIntros "Hleft Hright" (Hlength Hpointer).
  have HprocessedBound : (32 * processed <= length bytes)%nat by lia.
  have Hsplit :
      take (32 * processed + 8) bytes =
        take (32 * processed) bytes ++
          take 8 (drop (32 * processed) bytes).
  { rewrite take_take_drop. f_equal. }
  iAssert (base ↦ₘ∗
    (take (32 * processed) bytes ++
      take 8 (drop (32 * processed) bytes)))%I with "[Hleft]"
    as "HsplitLeft".
  { rewrite -Hsplit. iExact "Hleft". }
  iDestruct (mem_mapsto_array_app 8%N base (DfracOwn 1)
    (take (32 * processed) bytes)
    (take 8 (drop (32 * processed) bytes)) with "HsplitLeft") as
    "(Hdone & Hprefix)".
  have HtakeLength :
      length (take (32 * processed) bytes) = (32 * processed)%nat.
  { rewrite length_take Nat.min_l //. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * (32 * processed)%nat)%Z =
        bv_unsigned pointer.
  { rewrite Hpointer.
    change (base + 1 * Z.of_nat (32 * processed) =
      base + 32 * Z.of_nat processed)%Z.
    rewrite Nat2Z.inj_mul. lia. }
  iEval (rewrite HtakeLength HcurrentAddress) in "Hprefix".
  have Hdrop :
      drop (32 * processed + 9) bytes =
        drop 9 (drop (32 * processed) bytes).
  { rewrite drop_drop. f_equal. }
  iEval (rewrite Hdrop) in "Hright".
  have HrightAddress :
      (base + Z.of_nat (32 * processed + 9))%Z =
        (bv_unsigned pointer + 9)%Z.
  { rewrite Hpointer Nat2Z.inj_add Nat2Z.inj_mul. lia. }
  iEval (rewrite HrightAddress) in "Hright".
  iFrame "Hdone Hprefix Hright".
Qed.

Lemma write_success_blob_hashes_segment14_recombine_lbu
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed : nat)
    (bytes : list (bv 8)) (byte : bv 8) :
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  ⌜drop (32 * processed) bytes !! 8%nat = Some byte⌝ -∗
  base ↦ₘ∗ take (32 * processed) bytes -∗
  (bv_unsigned pointer + 8) ↦ₘ byte -∗
  bv_unsigned pointer ↦ₘ∗ take 8 (drop (32 * processed) bytes) -∗
  (bv_unsigned pointer + 9) ↦ₘ∗ drop 9 (drop (32 * processed) bytes) -∗
  base ↦ₘ∗ bytes.
Proof.
  iIntros (Hpointer Hlookup) "Hdone Hbyte Hprefix Hsuffix".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (bv_unsigned pointer) (drop (32 * processed) bytes) 8 byte
    (bv_unsigned pointer + 9) (bv_unsigned pointer + 8) with
    "Hprefix Hsuffix Hbyte [] [] []") as "Hcurrent".
  { iPureIntro. exact Hlookup. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * (32 * processed)%nat)%Z =
        bv_unsigned pointer.
  { rewrite Hpointer.
    change (base + 1 * Z.of_nat (32 * processed) =
      base + 32 * Z.of_nat processed)%Z.
    rewrite Nat2Z.inj_mul. lia. }
  have HprocessedBound : (32 * processed <= length bytes)%nat.
  { have Hindex : (8 < length (drop (32 * processed) bytes))%nat.
    { pose proof Hlookup as Hindex.
      apply lookup_lt_Some in Hindex. exact Hindex. }
    rewrite length_drop in Hindex. lia. }
  iEval (rewrite -HcurrentAddress) in "Hcurrent".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take (32 * processed) bytes) (drop (32 * processed) bytes)
    (32 * processed) with "Hdone Hcurrent") as "Harray".
  { rewrite length_take. apply Nat.min_l. exact HprocessedBound. }
  iEval (rewrite take_drop) in "Harray".
  iExact "Harray".
Qed.

Lemma write_success_blob_hashes_segment14_raw_registers
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 6%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x8" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx8".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 6%nat
    (KindReg "x8", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.
