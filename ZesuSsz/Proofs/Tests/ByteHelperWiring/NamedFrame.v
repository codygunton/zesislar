Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Definition production_frame (entry : bv 64) : bv 64 := (entry - BV 64 2000)%bv.

Lemma production_named_frame (entry : bv 64)
    (Hlower : 2176 <= bv_unsigned entry) :
  bv_unsigned (entry - BV 64 2048) = bv_unsigned (production_frame entry) - 48.
Proof. zesu_run. Qed.
Print Assumptions production_named_frame.
