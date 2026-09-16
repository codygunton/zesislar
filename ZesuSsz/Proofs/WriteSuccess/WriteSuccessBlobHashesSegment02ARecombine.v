Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma write_success_blob_hashes_segment02a_recombine_lbu
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed : nat)
    (bytes : list (bv 8)) (byte : bv 8) :
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  ⌜drop (32 * processed) bytes !! 18%nat = Some byte⌝ -∗
  base ↦ₘ∗ take (32 * processed) bytes -∗
  (bv_unsigned pointer + 18) ↦ₘ byte -∗
  bv_unsigned pointer ↦ₘ∗ take 18 (drop (32 * processed) bytes) -∗
  (bv_unsigned pointer + 19) ↦ₘ∗
    drop 19 (drop (32 * processed) bytes) -∗
  base ↦ₘ∗ bytes.
Proof.
  iIntros (Hpointer Hlookup) "Hdone Hbyte Hprefix Hsuffix".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (bv_unsigned pointer) (drop (32 * processed) bytes) 18 byte
    (bv_unsigned pointer + 19) (bv_unsigned pointer + 18) with
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
  { have Hindex : (18 < length (drop (32 * processed) bytes))%nat.
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
