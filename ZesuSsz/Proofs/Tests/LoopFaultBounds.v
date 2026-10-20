Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuMachineMap.Machine.
Open Scope Z_scope.

Lemma loop_readable_fault (ptr count cursor : Z) (storage : list (bv 8)) (index : nat) (value : bv 8) :
  storage !! index = Some value ->
  ptr <= cursor < ptr + Z.of_nat (length storage) * 1 ->
  0 <= cursor < 2^64 -> ptr <= cursor -> cursor+1 <= ptr+count ->
  ((mapInputBufferAddress defaultMap <= ptr /\
      ptr+count <= mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= ptr /\ ptr+count <= machineRamEnd defaultMap)) ->
  bv_signed (bv_zero_extend 128 ((Z_to_bv 64 cursor + 0)%bv)) <
    bv_signed (Z_to_bv 128 (mapRamBase defaultMap)) ->
  ~ (bv_signed (bv_zero_extend 128 ((Z_to_bv 64 cursor + 0)%bv) + 1)%bv <=
    bv_signed (Z_to_bv 128 (mapInputBufferAddress defaultMap + mapInputCapacity defaultMap))) -> False.
Proof. intros Hlookup Hrange Hcursor Hlower Hnext Hreadable Hlow Hfault. zesu_region_fault_if_enabled. Qed.

Lemma loop_missing_readable_refuses (storage : list (bv 8)) (index : nat) (value : bv 8) (base cursor : Z) :
 storage !! index = Some value ->
 base <= cursor < base + Z.of_nat (length storage) -> True.
Proof.
 intros Hlookup Hrange.
 Fail zesu_region_fault_readable_array_context.
 exact I.
Qed.

Lemma loop_missing_lookup_refuses (storage : list (bv 8)) (base cursor count low0 high0 low1 high1 : Z) :
 base <= cursor < base + Z.of_nat (length storage) ->
 ((low0 <= base /\ base + count <= high0) \/
  (low1 <= base /\ base + count <= high1)) -> True.
Proof.
 intros Hrange Hreadable.
 Fail zesu_region_fault_readable_array_context.
 exact I.
Qed.

Lemma readable_array_observed_stride (storage : list (bv 8)) (index : nat) (value : bv 8)
 (base cursor count low0 high0 low1 high1 : Z) :
 storage !! index = Some value ->
 base <= cursor + 0 < base + Z.of_nat (length storage) * Z.of_N (8 `div` 8) ->
 ((low0 <= base /\ base + count <= high0) \/
  (low1 <= base /\ base + count <= high1)) ->
 ~ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 cursor + 0)%bv + 1)%bv <= 0) -> True.
Proof.
 intros Hlookup Hrange Hreadable Hfault.
 zesu_region_fault_readable_array_context.
 exact I.
Qed.

Lemma readable_array_wrong_fault (storage : list (bv 8)) (index : nat) (value : bv 8)
 (base cursor other count low0 high0 low1 high1 : Z) :
 storage !! index = Some value ->
 base <= cursor < base + Z.of_nat (length storage) ->
 ((low0 <= base /\ base + count <= high0) \/
  (low1 <= base /\ base + count <= high1)) ->
 ~ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 other + 0)%bv + 1)%bv <= 0) -> True.
Proof.
 intros Hlookup Hrange Hreadable Hfault.
 Fail zesu_region_fault_readable_array_context.
 exact I.
Qed.

Lemma loop_unrelated_goal_refuses (ptr count cursor : Z) :
  0 <= cursor < 2^64 -> ptr <= cursor -> cursor+1 <= ptr+count ->
  ((mapInputBufferAddress defaultMap <= ptr /\
      ptr+count <= mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= ptr /\ ptr+count <= machineRamEnd defaultMap)) ->
  bv_signed (bv_zero_extend 128 ((Z_to_bv 64 cursor + 0)%bv)) <
    bv_signed (Z_to_bv 128 (mapRamBase defaultMap)) ->
  ~ (bv_signed (bv_zero_extend 128 ((Z_to_bv 64 cursor + 0)%bv) + 1)%bv <=
    bv_signed (Z_to_bv 128 (mapInputBufferAddress defaultMap + mapInputCapacity defaultMap))) -> True.
Proof.
  intros Hcursor Hlower Hnext Hreadable Hlow Hfault.
  Fail zesu_region_fault_if_enabled.
  exact I.
Qed.
