Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuMachineMap.Machine.
From stdpp Require Import list_numbers tactics.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation.VmClosed.
Require Import ZesuSsz.Automation.InstrPreAddress.
Require Import ZesuSsz.Automation.LookupReduce.
From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance vm_safety_low_mask : ZesuStepLowMask := I.

Lemma vm_closed_literal : True.
Proof. zesu_vm_closed (3 + 4)%Z. exact I. Qed.

Lemma vm_closed_local_definition : True.
Proof. pose (value := (3 + 4)%Z). zesu_vm_closed value. exact I. Qed.

Lemma vm_symbolic_refusal (value : Z) : True.
Proof. assert_fails ltac:(zesu_vm_closed value). exact I. Qed.

Lemma vm_symbolic_alias_refusal (value : Z) : True.
Proof.
  pose (alias := value).
  assert_fails ltac:(zesu_vm_closed alias).
  exact I.
Qed.

Lemma vm_evar_alias_refusal : True.
Proof.
  evar (value : Z).
  pose (first_alias := value).
  pose (second_alias := first_alias).
  assert_fails ltac:(zesu_vm_closed second_alias).
  instantiate (value := 0%Z).
  exact I.
Qed.

Lemma vm_little_endian_literal : Z_to_little_endian 1 8 5 = [5].
Proof. zesu_finish_little_endian_if_closed. Qed.

Lemma vm_little_endian_symbolic_fallback (value : Z) :
  Z_to_little_endian 1 8 value = Z_to_little_endian 1 8 value.
Proof.
  assert_fails ltac:(idtac; zesu_finish_little_endian_if_closed).
  reflexivity.
Qed.

Lemma vm_low_mask_symbolic_value (value : bv 64) :
  bv_unsigned (bv_and (bv_add value (Z_to_bv 64 1))
    (Z_to_bv 64 (Z.ones 8))) =
  bv_unsigned (Z_to_bv 8 (bv_unsigned value + 1)).
Proof. zesu_low_mask_if_closed. Qed.

Lemma vm_low_mask_symbolic_offset_fallback (value offset : bv 64)
    (expected : bv_unsigned (bv_and (bv_add value offset)
      (Z_to_bv 64 (Z.ones 8))) =
      bv_unsigned (Z_to_bv 8 (bv_unsigned value + 1))) :
  bv_unsigned (bv_and (bv_add value offset) (Z_to_bv 64 (Z.ones 8))) =
  bv_unsigned (Z_to_bv 8 (bv_unsigned value + 1)).
Proof.
  pose (sum := bv_add value offset).
  pose (masked := bv_and sum (Z_to_bv 64 (Z.ones 8))).
  change (bv_unsigned masked = bv_unsigned (Z_to_bv 8 (bv_unsigned value + 1))).
  first [solve [zesu_low_mask_if_closed] |
    lazymatch goal with |- bv_unsigned ?current = _ => constr_eq current masked end;
    exact expected].
Qed.

Lemma vm_array_direct_literal (bytes : list (bv 8)) (byte : bv 8) :
  bytes !! Z.to_nat (bv_unsigned (Z_to_bv 64 0) `div` 1) = Some byte ->
  default (Z_to_bv 8 0) (bytes !! 0%nat) = byte.
Proof. intros Hlookup. zesu_finish_array_byte_lookup_if_closed. Qed.

Lemma vm_array_direct_symbolic_refusal
    (bytes : list (bv 8)) (byte : bv 8) (offset : bv 64) :
  bytes !! Z.to_nat (bv_unsigned offset `div` 1) = Some byte -> True = True.
Proof.
  intros Hlookup.
  assert_fails ltac:(idtac; zesu_finish_array_byte_lookup_if_closed).
  reflexivity.
Qed.

Lemma vm_array_pre_normalized_literal
    (bytes : list (bv 8)) (byte : bv 8) (row : bv 64) (base : Z) (index : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (index + 0 <= length bytes)%nat ->
  bytes !! Z.to_nat
    ((bv_unsigned (bv_add row (Z_to_bv 64 0)) - base) `div` 1) = Some byte ->
  default (Z_to_bv 8 0) (bytes !! (index + 0)%nat) = byte.
Proof.
  intros Hcursor Hlower Hupper Hbound Hlookup.
  zesu_finish_array_byte_lookup_if_closed.
Qed.

Lemma vm_array_pre_normalized_symbolic_refusal
    (bytes : list (bv 8)) (byte : bv 8) (row offset : bv 64) (base : Z) :
  bytes !! Z.to_nat ((bv_unsigned (bv_add row offset) - base) `div` 1) = Some byte ->
  True = True.
Proof.
  intros Hlookup.
  assert_fails ltac:(idtac; zesu_finish_array_byte_lookup_if_closed).
  reflexivity.
Qed.

Lemma vm_array_pre_normalized_no_div_refusal
    (bytes : list (bv 8)) (byte : bv 8) (row offset : bv 64) (base : Z) :
  bytes !! Z.to_nat (bv_unsigned (bv_add row offset) - base) = Some byte ->
  True = True.
Proof.
  intros Hlookup.
  assert_fails ltac:(idtac; zesu_finish_array_byte_lookup_if_closed).
  reflexivity.
Qed.
