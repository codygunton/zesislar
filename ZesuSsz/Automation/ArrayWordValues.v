Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.

Ltac zesu_array_word_value :=
  rewrite ?array_byte_pair_value16 ?array_byte_pair_value;
  apply array_byte_four_value.
