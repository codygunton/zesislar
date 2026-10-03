Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma production_constant_word_index (base : Z) :
  ZesuSsz.Contracts.IslarisMemory.array_region_start 64 (base + 936) (base + 984) = 6%nat.
Proof. zesu_run. Qed.
Print Assumptions production_constant_word_index.
