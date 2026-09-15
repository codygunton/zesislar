Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

Lemma machine_bound_selector_source_form (sp : bv 64) :
  (bv_unsigned sp < machineRamEnd defaultMap)%Z ->
  (bv_unsigned sp < machineRamEnd defaultMap)%Z.
Proof.
  intros Hsource.
  zesu_name_machine_bound
    ((bv_unsigned sp < machineRamEnd defaultMap)%Z) Hbound.
  exact Hbound.
Qed.
Print Assumptions machine_bound_selector_source_form.

Lemma machine_bound_selector_reduced_form (sp : bv 64) :
  (bv_unsigned sp < machineRamEnd defaultMap)%Z ->
  (bv_unsigned sp < machineRamEnd defaultMap)%Z.
Proof.
  intros Hreduced.
  zesu_normalize_machine_map.
  zesu_name_machine_bound
    ((bv_unsigned sp < machineRamEnd defaultMap)%Z) Hbound.
  exact Hbound.
Qed.
Print Assumptions machine_bound_selector_reduced_form.
