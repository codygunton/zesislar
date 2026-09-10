Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition writeOutputEvents (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

