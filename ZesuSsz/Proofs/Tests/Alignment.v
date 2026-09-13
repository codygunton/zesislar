Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Alignment.
Require Import isla.riscv64.riscv64.

Lemma alignment_word_offset (pointer : bv 64) :
  bv_extract 0 3 pointer = BV 3 0 ->
  bv_extract 0 3 (pointer + BV 64 8)%bv = BV 3 0.
Proof. intros Halign. zesu_alignment. Qed.
Print Assumptions alignment_word_offset.

Lemma alignment_stack_word (pointer : bv 64) :
  bv_extract 0 4 pointer = BV 4 0 ->
  bv_extract 0 3 (pointer - BV 64 48)%bv = BV 3 0.
Proof. intros Halign. zesu_alignment. Qed.
Print Assumptions alignment_stack_word.

Lemma alignment_cancel_offset (pointer : bv 64) :
  bv_extract 0 3 pointer = BV 3 0 ->
  bv_extract 0 3 (pointer + BV 64 8 + BV 64 18446744073709551608)%bv = BV 3 0.
Proof. intros Halign. zesu_alignment. Qed.
Print Assumptions alignment_cancel_offset.
