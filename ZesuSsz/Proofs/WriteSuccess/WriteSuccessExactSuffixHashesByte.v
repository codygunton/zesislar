Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Definition suffixWordByte (source : list (bv 8)) (index : nat) : bv 64 :=
  bv_zero_extend 64 (default (BV 8 0) (source !! index)).
