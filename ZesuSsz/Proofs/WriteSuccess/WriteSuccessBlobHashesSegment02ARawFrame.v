Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma write_success_blob_hashes_segment02_raw_frame
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed remaining : nat)
    (bytes : list (bv 8)) :
  base ↦ₘ∗ take (32 * processed + 18) bytes -∗
  (base + Z.of_nat (32 * processed + 19)) ↦ₘ∗
    drop (32 * processed + 19) bytes -∗
  ⌜length bytes = (32 * (processed + S remaining))%nat⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  let byte := default (BV 8 0) (bytes !! (32 * processed + 18)%nat) in
  base ↦ₘ∗ take (32 * processed) bytes ∗
  bv_unsigned pointer ↦ₘ∗ take 18 (drop (32 * processed) bytes) ∗
  (bv_unsigned pointer + 19) ↦ₘ∗ drop 19 (drop (32 * processed) bytes).
Proof.
  iIntros "Hleft Hright" (Hlength Hpointer).
  have HprocessedBound : (32 * processed <= length bytes)%nat by lia.
  have Hsplit :
      take (32 * processed + 18) bytes =
        take (32 * processed) bytes ++
          take 18 (drop (32 * processed) bytes).
  { rewrite take_take_drop. f_equal. }
  iAssert (base ↦ₘ∗
    (take (32 * processed) bytes ++
      take 18 (drop (32 * processed) bytes)))%I with "[Hleft]"
    as "HsplitLeft".
  { rewrite -Hsplit. iExact "Hleft". }
  iDestruct (mem_mapsto_array_app 8%N base (DfracOwn 1)
    (take (32 * processed) bytes)
    (take 18 (drop (32 * processed) bytes)) with "HsplitLeft") as
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
      drop (32 * processed + 19) bytes =
        drop 19 (drop (32 * processed) bytes).
  { rewrite drop_drop. f_equal. }
  iEval (rewrite Hdrop) in "Hright".
  have HrightAddress :
      (base + Z.of_nat (32 * processed + 19))%Z =
        (bv_unsigned pointer + 19)%Z.
  { rewrite Hpointer Nat2Z.inj_add Nat2Z.inj_mul. lia. }
  iEval (rewrite HrightAddress) in "Hright".
  iFrame "Hdone Hprefix Hright".
Qed.
