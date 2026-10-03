Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.

Lemma test_byte_index_fact_selection (bytes : list (bv 8))
    (index : nat) (pointer other : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  bv_unsigned other mod 17 = 0%Z ->
  (index + 20 < length bytes)%nat.
Proof.
  intros Hindex Hbound Hunrelated.
  zesu_select_index_facts bytes index pointer base.
  Fail pose proof Hunrelated.
  zesu_finish_lia.
Qed.

Lemma test_arithmetic_timeout_retains_goal : True.
Proof.
  zesu_bounded_arithmetic ltac:(idtac).
  Fail zesu_bounded_arithmetic_with 1
    ltac:(let rec spin dummy := spin dummy in spin tt).
  exact I.
Qed.

Print Assumptions test_byte_index_fact_selection.
Print Assumptions test_arithmetic_timeout_retains_goal.

Lemma test_byte_pointer_ram_bound (bytes : list (bv 8)) (index : nat)
    (pointer other : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned other mod 17 = 0%Z ->
  (bv_unsigned (pointer + BV 64 28) <= bv_unsigned (BV 64 (machineRamEnd defaultMap - 1)))%Z.
Proof.
  intros Hindex Hbound Hram Hbase Hunrelated.
  zesu_byte_index_arithmetic.
Qed.

Lemma test_byte_pointer_array_range (bytes : list (bv 8)) (index : nat)
    (pointer other : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned other mod 17 = 0%Z ->
  ((base <= bv_unsigned (pointer + BV 64 23) < base + Z.of_nat (length bytes))%Z \/
    base = bv_unsigned (pointer + BV 64 23)).
Proof.
  intros Hindex Hbound Hram Hbase Hunrelated.
  bv_solve.
Qed.

Print Assumptions test_byte_pointer_ram_bound.
Print Assumptions test_byte_pointer_array_range.

Lemma test_byte_pointer_address_normalization (bytes : list (bv 8)) (index : nat)
    (pointer other : bv 64) (base : Z) (loaded : bv 8) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned other mod 17 = 0%Z ->
  bytes !! Z.to_nat (bv_unsigned (pointer + BV 64 16) - base) = Some loaded ->
  (Z.to_nat (bv_unsigned (pointer + BV 64 16) - base) < length bytes)%nat ->
  bv_unsigned (pointer + BV 64 28) = (bv_unsigned pointer + 28)%Z.
Proof.
  intros Hindex Hbound Hram Hbase Hunrelated Hloaded Hcursor.
  zesu_byte_index_arithmetic.
Qed.

Print Assumptions test_byte_pointer_address_normalization.

Lemma test_byte_array_interior_pointer_root `{!islaG Sigma}
    (bytes : list (bv 8)) (index : nat) (pointer : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  base ↦ₘ∗ bytes -∗ base ↦ₘ∗ bytes.
Proof.
  intros Hindex. iIntros "Harray".
  lazymatch goal with
  | |- environments.envs_entails ?Delta _ =>
      let spatial := eval cbn [environments.env_spatial] in
        (environments.env_spatial Delta) in
      zesu_has_initialized_array_root pointer spatial
  end.
  iExact "Harray".
Qed.

Print Assumptions test_byte_array_interior_pointer_root.

Lemma test_byte_pointer_array_lookup `{!islaG Sigma}
    (bytes : list (bv 8)) (index : nat) (pointer : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned pointer + 29))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop base (MKArray 8 base bytes)) (base ↦ₘ∗ bytes).
Proof.
  intros Hindex Hbound Hram Hbase.
  typeclasses eauto.
Qed.

Print Assumptions test_byte_pointer_array_lookup.

Lemma test_byte_pointer_shelved_ram_bound
    (pointer : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (loaded : bv 8)
    (Hbase : (mapRamBase defaultMap <= base)%Z)
    (Hram : (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z)
    (Hbound : (index + 31 < length bytes)%nat)
    (Hindex : bv_unsigned pointer = (base + Z.of_nat index)%Z)
    (Hloaded : bytes !! Z.to_nat ((bv_unsigned (pointer + 23) - base) `div` 1) = Some loaded) :
  SHELVED_SIDECOND
    (Val_Bool (bool_decide (bv_unsigned (pointer + 28) <=
      bv_unsigned (0 + 1073741824 - 1 : bv 64))%Z) = Val_Bool true).
Proof. zesu_finish. Qed.

Print Assumptions test_byte_pointer_shelved_ram_bound.

Lemma test_stack_byte_trace_cursor `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (event : seq_event) (accept : nat -> seq_snapshot -> Prop)
    (tail : spec) (address : Z) (P : iProp Sigma) :
  (mapRamBase defaultMap <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned sp + 1784 < machineRamEnd defaultMap)%Z ->
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons_snap event
        (accept (Z.to_nat (bv_unsigned (sp + BV 64 1752) -
          (bv_unsigned sp + 1744)))) x.1ₗ ⊆
      scons_snap event (accept 8%nat) tail⌝ ∗ instr_pre address P.
Proof.
  intros Hlow Hhigh. iIntros "Hpre".
  zesu_finish. zesu_close_matching_trace_tail. iExact "Hpre".
Qed.

Print Assumptions test_stack_byte_trace_cursor.

Lemma test_scalar_byte_pointer_ram_bound
    (pointer : bv 64) (base : Z) (bytes : list (bv 8))
    (processed remaining : nat) (loaded : bv 8)
    (Hbase : (mapRamBase defaultMap <= base)%Z)
    (Hram : (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z)
    (Hindex : bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z)
    (Hlength : length bytes = (32 * (processed + S remaining))%nat)
    (H25 : bytes !! Z.to_nat ((bv_unsigned (pointer + 25) - base) `div` 1) = Some loaded)
    (H24 : bytes !! Z.to_nat ((bv_unsigned (pointer + 24) - base) `div` 1) = Some loaded)
    (H26 : bytes !! Z.to_nat ((bv_unsigned (pointer + 26) - base) `div` 1) = Some loaded)
    (H27 : bytes !! Z.to_nat ((bv_unsigned (pointer + 27) - base) `div` 1) = Some loaded)
    (H28 : bytes !! Z.to_nat ((bv_unsigned (pointer + 28) - base) `div` 1) = Some loaded)
    (H29 : bytes !! Z.to_nat ((bv_unsigned (pointer + 29) - base) `div` 1) = Some loaded)
    (H30 : bytes !! Z.to_nat ((bv_unsigned (pointer + 30) - base) `div` 1) = Some loaded) :
  (bv_unsigned (pointer + 31) <=
    bv_unsigned (0 + 1073741824 - 1 : bv 64))%Z.
Proof. timeout 2 zesu_byte_pointer_arithmetic. Qed.
Print Assumptions test_scalar_byte_pointer_ram_bound.

Lemma test_scalar_byte_pointer_array_coverage
    (pointer : bv 64) (base : Z) (bytes : list (bv 8))
    (processed remaining : nat) (loaded : bv 8)
    (Hbase : (mapRamBase defaultMap <= base)%Z)
    (Hram : (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z)
    (Hindex : bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z)
    (Hlength : length bytes = (32 * (processed + S remaining))%nat)
    (H25 : bytes !! Z.to_nat ((bv_unsigned (pointer + 25) - base) `div` 1) = Some loaded)
    (H24 : bytes !! Z.to_nat ((bv_unsigned (pointer + 24) - base) `div` 1) = Some loaded)
    (H26 : bytes !! Z.to_nat ((bv_unsigned (pointer + 26) - base) `div` 1) = Some loaded)
    (H27 : bytes !! Z.to_nat ((bv_unsigned (pointer + 27) - base) `div` 1) = Some loaded)
    (H28 : bytes !! Z.to_nat ((bv_unsigned (pointer + 28) - base) `div` 1) = Some loaded)
    (H29 : bytes !! Z.to_nat ((bv_unsigned (pointer + 29) - base) `div` 1) = Some loaded)
    (H30 : bytes !! Z.to_nat ((bv_unsigned (pointer + 30) - base) `div` 1) = Some loaded) :
  (base <= bv_unsigned (pointer + 31) < base + Z.of_nat (length bytes))%Z.
Proof. timeout 2 zesu_byte_pointer_arithmetic. Qed.
Print Assumptions test_scalar_byte_pointer_array_coverage.

Lemma test_scalar_byte_pointer_rule_selection `{!islaG Sigma} `{!threadG}
    (pointer : bv 64)
    (base : Z)
    (processed : nat)
    (remaining : nat)
    (bytes : list (bv 8))
    (H0 : (base + length bytes < 0 + 1073741824)%Z)
    (H1 : (0 ≤ base)%Z)
    (H6 : bv_unsigned pointer = (base + 32 * processed)%Z)
    (H7 : length bytes = (32 * (processed + S remaining))%nat)
    (Hpower : (S remaining < 2 ^ 64)%nat)
    (vmem : bv 8)
    (H28 : bytes !! Z.to_nat ((bv_unsigned (pointer + 25) - base) `div` 1) = Some vmem)
    (H29 : (Z.to_nat ((bv_unsigned (pointer + 25) - base) `div` 1) < length bytes)%nat)
    (vmem0 : bv 8)
    (H32 : bytes !! Z.to_nat ((bv_unsigned (pointer + 24) - base) `div` 1) = Some vmem0)
    (H33 : (Z.to_nat ((bv_unsigned (pointer + 24) - base) `div` 1) < length bytes)%nat)
    (vmem1 : bv 8)
    (H36 : bytes !! Z.to_nat ((bv_unsigned (pointer + 26) - base) `div` 1) = Some vmem1)
    (H37 : (Z.to_nat ((bv_unsigned (pointer + 26) - base) `div` 1) < length bytes)%nat)
    (vmem2 : bv 8)
    (H40 : bytes !! Z.to_nat ((bv_unsigned (pointer + 27) - base) `div` 1) = Some vmem2)
    (H41 : (Z.to_nat ((bv_unsigned (pointer + 27) - base) `div` 1) < length bytes)%nat)
    (vmem3 : bv 8)
    (H46 : bytes !! Z.to_nat ((bv_unsigned (pointer + 28) - base) `div` 1) = Some vmem3)
    (H47 : (Z.to_nat ((bv_unsigned (pointer + 28) - base) `div` 1) < length bytes)%nat)
    (vmem4 : bv 8)
    (H50 : bytes !! Z.to_nat ((bv_unsigned (pointer + 29) - base) `div` 1) = Some vmem4)
    (H51 : (Z.to_nat ((bv_unsigned (pointer + 29) - base) `div` 1) < length bytes)%nat)
    (vmem5 : bv 8)
    (H54 : bytes !! Z.to_nat ((bv_unsigned (pointer + 30) - base) `div` 1) = Some vmem5)
    (H55 : (Z.to_nat ((bv_unsigned (pointer + 30) - base) `div` 1) < length bytes)%nat) :
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned pointer + 31))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop base (MKArray 8 base bytes)) (base ↦ₘ∗ bytes).
Proof.
  apply tac_mem_mapsto_array_eq.
  timeout 2 bv_solve.
Qed.

Print Assumptions test_scalar_byte_pointer_rule_selection.

Lemma test_reverse_stack_pointer_bound (sp : bv 64)
  (Hbound : (bv_unsigned (sp - 2000) + 312 < 1073741824)%Z) :
  (0 <= bv_unsigned sp - 1976)%Z.
Proof. timeout 2 bv_solve. Qed.
Print Assumptions test_reverse_stack_pointer_bound.

Lemma test_reverse_stack_wrap_rejected (sp : bv 64)
    (Hbound : (bv_unsigned (sp - 2000) + 312 < bv_modulus 64)%Z) : True.
Proof.
  Fail assert (Hinvalid : (0 <= bv_unsigned sp - 1976)%Z)
    by zesu_stack_pointer_arithmetic.
  exact I.
Qed.

Lemma test_binary_successor_power_bound (n base exponent : nat) :
  (S n < base ^ exponent)%nat <->
  (Z.of_nat n + 1 < Z.of_nat base ^ Z.of_nat exponent)%Z.
Proof.
  rewrite Nat2Z.inj_lt Nat2Z.inj_succ Nat2Z.inj_pow.
  rewrite Z.add_1_r. reflexivity.
Qed.
Print Assumptions test_binary_successor_power_bound.

Lemma test_binary_successor_power_le_bound (n base exponent : nat) :
  (S n <= base ^ exponent)%nat <->
  (Z.of_nat n + 1 <= Z.of_nat base ^ Z.of_nat exponent)%Z.
Proof.
  rewrite Nat2Z.inj_le Nat2Z.inj_succ Nat2Z.inj_pow.
  rewrite Z.add_1_r. reflexivity.
Qed.
Print Assumptions test_binary_successor_power_le_bound.

Lemma test_reverse_stack_nested_address (sp : bv 64)
    (Hbound : bv_unsigned (sp - BV 64 2000) + 312 < 1073741824) :
  bv_unsigned (sp - BV 64 2000 + BV 64 24) = bv_unsigned sp - 1976.
Proof. bv_solve. Qed.
Print Assumptions test_reverse_stack_nested_address.
