Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Z_scope.
Lemma test_word_lookup_inactive (sp data size loaded loadedSize : bv 64)
    (Hlow : mapRamBase defaultMap <= bv_unsigned sp - 80)
    (Hhigh : bv_unsigned sp + 1896 < machineRamEnd defaultMap) :
  [data; size] !! Z.to_nat
    ((bv_unsigned (sp + BV 64 920)%bv - (bv_unsigned sp + 920)) `div` 8) = Some loaded ->
  [data; size] !! Z.to_nat
    ((bv_unsigned (sp + BV 64 928)%bv - (bv_unsigned sp + 920)) `div` 8) = Some loadedSize ->
  True.
Proof.
  intros Hlookup Hlookup0.
  Fail zesu_word_array_lookup_if_enabled.
  exact I.
Qed.
Print Assumptions test_word_lookup_inactive.

Local Instance private_word_lookup_switch : ZesuStepWordArrayLookup := I.
Lemma test_word_lookup_exact (sp data size loaded loadedSize : bv 64)
    (Hlow : mapRamBase defaultMap <= bv_unsigned sp - 80)
    (Hhigh : bv_unsigned sp + 1896 < machineRamEnd defaultMap) :
  [data; size] !! Z.to_nat
    ((bv_unsigned (sp + BV 64 920)%bv - (bv_unsigned sp + 920)) `div` 8) = Some loaded ->
  [data; size] !! Z.to_nat
    ((bv_unsigned (sp + BV 64 928)%bv - (bv_unsigned sp + 920)) `div` 8) = Some loadedSize ->
  loaded = data /\ loadedSize = size.
Proof.
  intros Hlookup Hlookup0.
  time "wrapped word lookup candidate" repeat zesu_word_array_lookup_if_enabled.
  split; reflexivity.
Qed.
Print Assumptions test_word_lookup_exact.
