Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List Lia.
Require Import ZesuSsz.Automation2.All.

Lemma array_region_updated_bytes (p : Z) (bytes : list (bv 8))
    (Hlength : length bytes = 40%nat) :
  (p <= p + 8 < p + Z.of_nat (length
    (take 0 (take 32 bytes ++ [0%bv; 0%bv] ++ drop 34 bytes) ++
     replicate 8 (0%bv : bv 8) ++
     drop 8 (take 32 bytes ++ [0%bv; 0%bv] ++ drop 34 bytes))))%Z.
Proof. ZesuSsz.Automation2.UninitRegions.zesu_region_bounds. Qed.

Lemma array_region_reject_outside (p : Z) (bytes : list (bv 8))
    (Hlength : length bytes = 40%nat) : True.
Proof.
  Fail assert (Hbad : (p <= p + 40 < p + Z.of_nat (length
    (take 32 bytes ++ [0%bv; 0%bv] ++ drop 34 bytes)))%Z)
    by ZesuSsz.Automation2.UninitRegions.zesu_region_bounds.
  exact I.
Qed.

Print Assumptions array_region_updated_bytes.

Lemma array_region_updated_selector `{!islaG Sigma} `{!threadG}
    (p : Z) (bytes : list (bv 8))
    (Hlength : length bytes = 40%nat)
    (Hbounds : 0 <= p /\ p + 40 < 2 ^ 64) :
  p ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - p))
      (take (Z.to_nat (p + 32 - p)) bytes ++ [0%bv; 0%bv] ++
       drop (Z.to_nat (p + 32 - p) + 2) bytes) ++
     replicate 8 (0%bv : bv 8) ++
     drop (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - p) + 8)
      (take (Z.to_nat (p + 32 - p)) bytes ++ [0%bv; 0%bv] ++
       drop (Z.to_nat (p + 32 - p) + 2) bytes)) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 p + 8)))
    (fun _ => True)%I.
Proof.
  iStartProof. iIntros "Hbytes".
  ZesuSsz.Automation2.Hooks.zesu_integer_array_address_if_enabled.
  ZesuSsz.Automation2.Finish.zesu_run.
Qed.
Print Assumptions array_region_updated_selector.

Lemma array_region_captured_800d69b0 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs)
    (Hlength : length (decodeItemBeforeStorage args) = 40%nat)
    (Hlower : 0 <= decodeItemOutputPointer args)
    (Hupper : decodeItemOutputPointer args + 40 < 2 ^ 64) :
  (decodeItemOutputPointer args
 ↦ₘ∗ (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)) - decodeItemOutputPointer args))
        (take (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args)) (decodeItemBeforeStorage args) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8))
         :: Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) :: drop (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) + N.to_nat 2) (decodeItemBeforeStorage args)) ++
      Z_to_bv 8 (Z.land (bv_unsigned (1 : bv 64)) (Z.ones 8))
      :: Z_to_bv 8 (Z.land (bv_unsigned (1 : bv 64) ≫ 8) (Z.ones 8))
         :: Z_to_bv 8 (Z.land ((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) (Z.ones 8))
            :: Z_to_bv 8 (Z.land (((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
               :: Z_to_bv 8 (Z.land ((((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                  :: Z_to_bv 8 (Z.land (((((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                     :: Z_to_bv 8 (Z.land ((((((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                        :: Z_to_bv 8 (Z.land (((((((bv_unsigned (1 : bv 64) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                           :: drop (Z.to_nat (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)) - decodeItemOutputPointer args) + N.to_nat 8)
                                (take (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args)) (decodeItemBeforeStorage args) ++
                                 Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8))
                                 :: Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8))
                                    :: drop (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) + N.to_nat 2) (decodeItemBeforeStorage args))))%I -∗
  find_in_context (FindMemMapsTo
    (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args) + 8)))
    (fun _ => True)%I.
Proof.
  iStartProof. iIntros "Hbytes".
  ZesuSsz.Automation2.Hooks.zesu_integer_array_address_if_enabled.
  ZesuSsz.Automation2.Finish.zesu_run.
Qed.
Print Assumptions array_region_captured_800d69b0.

Lemma array_region_captured_800d6a78 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (w : bv 64)
    (Hlength : length (decodeItemBeforeStorage args) = 40%nat)
    (Hlower : 0 <= decodeItemOutputPointer args)
    (Hupper : decodeItemOutputPointer args + 40 < 2 ^ 64) :
  (decodeItemOutputPointer args
 ↦ₘ∗ (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)) - decodeItemOutputPointer args))
        (take (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args)) (decodeItemBeforeStorage args) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8))
         :: Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) :: drop (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) + N.to_nat 2) (decodeItemBeforeStorage args)) ++
      Z_to_bv 8 (Z.land (bv_unsigned w) (Z.ones 8))
      :: Z_to_bv 8 (Z.land (bv_unsigned w ≫ 8) (Z.ones 8))
         :: Z_to_bv 8 (Z.land ((bv_unsigned w ≫ 8) ≫ 8) (Z.ones 8))
            :: Z_to_bv 8 (Z.land (((bv_unsigned w ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
               :: Z_to_bv 8 (Z.land ((((bv_unsigned w ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                  :: Z_to_bv 8 (Z.land (((((bv_unsigned w ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                     :: Z_to_bv 8 (Z.land ((((((bv_unsigned w ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                        :: Z_to_bv 8 (Z.land (((((((bv_unsigned w ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                           :: drop (Z.to_nat (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)) - decodeItemOutputPointer args) + N.to_nat 8)
                                (take (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args)) (decodeItemBeforeStorage args) ++
                                 Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8))
                                 :: Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8))
                                    :: drop (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) + N.to_nat 2) (decodeItemBeforeStorage args))))%I -∗
  find_in_context (FindMemMapsTo
    (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args) + 8)))
    (fun _ => True)%I.
Proof.
  iStartProof. iIntros "Hbytes".
  ZesuSsz.Automation2.Hooks.zesu_integer_array_address_if_enabled.
  ZesuSsz.Automation2.Finish.zesu_run.
Qed.
Print Assumptions array_region_captured_800d6a78.
