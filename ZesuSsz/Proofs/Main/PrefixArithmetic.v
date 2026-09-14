Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Lemma main_prefix_stack_offset D offset :
  mapRamBase defaultMap + 0x880 <= D ->
  D + 0x7d0 < machineRamEnd defaultMap -> 0 <= offset <= 896 ->
  bv_unsigned (Z_to_bv 64 D + Z_to_bv 64 offset)%bv = D + offset.
Proof.
  intros Hlow Hhigh Hoffset.
  zesu_normalize_machine_map.
  bv_solve.
Qed.
Lemma main_prefix_input_size (bytes : list Z) :
  (length bytes <= maxSszInputSize)%nat ->
  bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))) = Z.of_nat (length bytes).
Proof.
  intros Hbound. pose proof (Nat2Z.is_nonneg (length bytes)).
  apply Nat2Z.inj_le in Hbound. unfold maxSszInputSize in Hbound.
  rewrite !Nat2Z.inj_mul in Hbound. cbn in Hbound. bv_solve.
Qed.
Print Assumptions main_prefix_stack_offset.
Print Assumptions main_prefix_input_size.

Lemma main_prefix_stack_alignment D :
  D `mod` 16 = 0 -> mapRamBase defaultMap + 0x880 <= D ->
  D + 0x7d0 < machineRamEnd defaultMap ->
  D `mod` 8 = 0 /\ bv_extract 0 3 (Z_to_bv 64 D) = BV 3 0 /\
    bv_extract 0 3 (Z_to_bv 64 D + BV 64 8)%bv = BV 3 0.
Proof.
  intros Halign Hlow Hhigh.
  zesu_normalize_machine_map.
  apply Z.mod_divide in Halign; last lia.
  destruct Halign as [k ->].
  have H8 : (k * 16) `mod` 8 = 0.
  { replace (k * 16) with ((k * 2) * 8) by ring. apply Z.mod_mul. lia. }
  have Hbits : bv_extract 0 3 (Z_to_bv 64 (k * 16)) = BV 3 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 (k * 16) ltac:(unfold bv_modulus; cbn; lia)).
    change ((k * 16) `mod` 8 = 0). exact H8. }
  split; first exact H8. split; first exact Hbits.
  rewrite bv_extract_0_bv_add_distr; last done. rewrite Hbits. bv_solve.
Qed.
Print Assumptions main_prefix_stack_alignment.
