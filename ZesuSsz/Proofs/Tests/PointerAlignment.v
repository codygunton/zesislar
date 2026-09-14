Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma finish_pointer_alignment_narrow (sp : bv 64) :
  bv_extract 0 4 sp = BV 4 0 -> bv_extract 0 3 sp = BV 3 0.
Proof. intros Halign. zesu_finish_pointer_alignment. Qed.

Lemma finish_pointer_alignment_offset (sp : bv 64) :
  bv_extract 0 4 sp = BV 4 0 ->
  bv_extract 0 3 (sp + BV 64 1664)%bv = BV 3 0.
Proof. intros Halign. zesu_finish_pointer_alignment. Qed.

Print Assumptions finish_pointer_alignment_narrow.
Print Assumptions finish_pointer_alignment_offset.
