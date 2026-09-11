Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.

Ltac zesu_saturate_alignment :=
  match goal with
  | H : bv_extract 0 _ _ = _ |- _ => bv_saturate
  | H : Z.land (bv_unsigned _) _ = _ |- _ => bv_saturate
  end.

Ltac zesu_finish :=
  prepare_sidecond;
  try assumption;
  try zesu_saturate_alignment;
  try bv_solve;
  try lia.

Ltac zesu_run :=
  unshelve liARun;
  zesu_finish.

Ltac zesu_block :=
  iStartProof;
  zesu_run.

Tactic Notation "zesu_pack" constr(witness) :=
  iExists witness;
  iFrame;
  try done;
  try zesu_finish.
