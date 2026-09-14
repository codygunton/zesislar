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
  change (2176 <= D) in Hlow. change (D + 2000 < 1073741824) in Hhigh.
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
