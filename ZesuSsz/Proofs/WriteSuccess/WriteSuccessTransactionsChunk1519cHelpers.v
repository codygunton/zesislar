Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Lemma write_success_transactions_chunk_1519c_offset (sp : bv 64) :
  (bv_unsigned sp < (machineRamEnd defaultMap))%Z ->
  bv_unsigned (sp + BV 64 128)%bv = bv_unsigned sp + 128.
Proof.
  intro Hupper. rewrite bv_add_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 sp).
  pose proof (bv_unsigned_in_range 64 (BV 64 128)).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma write_success_transactions_chunk_1519c_alignment (sp : bv 64) :
  (bv_unsigned sp `mod` 16 = 0)%Z ->
  (bv_unsigned sp < (machineRamEnd defaultMap))%Z ->
  bv_extract 0 3 (sp + BV 64 128)%bv = BV 3 0.
Proof.
  intros Halign Hupper. apply bv_eq.
  rewrite bv_extract_0_unsigned.
  rewrite (write_success_transactions_chunk_1519c_offset sp Hupper).
  rewrite !bv_unsigned_BV. unfold bv_wrap, bv_modulus. cbn.
  rewrite Z.add_mod; try lia.
Qed.

Lemma write_success_transactions_chunk_1519c_lower (sp : bv 64) :
  ((mapRamBase defaultMap) <= bv_unsigned sp)%Z ->
  (bv_unsigned sp < (machineRamEnd defaultMap))%Z ->
  (bv_unsigned (sp + BV 64 128)%bv >= bv_unsigned (BV 64 (mapRamBase defaultMap)))%Z.
Proof.
  intros Hlower Hupper.
  rewrite (write_success_transactions_chunk_1519c_offset sp Hupper).
  rewrite bv_unsigned_BV. lia.
Qed.

Lemma write_success_transactions_chunk_1519c_upper (sp : bv 64) :
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z ->
  (bv_unsigned (sp + BV 64 128)%bv <=
    bv_unsigned (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap) - BV 64 8))%Z.
Proof.
  intro Hupper.
  have Hoffset : (bv_unsigned sp < (machineRamEnd defaultMap))%Z by lia.
  rewrite (write_success_transactions_chunk_1519c_offset sp Hoffset).
  rewrite bv_unsigned_BV.
  change (bv_unsigned sp + 128 <= (machineRamEnd defaultMap - 8))%Z.
  lia.
Qed.
