Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma production_constant_word_lookup (sp : bv 64)
    (w0 w1 w2 w3 w4 w5 w6 loaded : bv 64)
    (Hbound : bv_unsigned sp + 984 < 2 ^ 64)
    (Hlookup : [w0; w1; w2; w3; w4; w5; w6] !!
      Z.to_nat ((bv_unsigned (sp + BV 64 984) - (bv_unsigned sp + 936)) `div` 8) = Some loaded) :
  loaded = w6.
Proof. zesu_run. Qed.
Print Assumptions production_constant_word_lookup.
