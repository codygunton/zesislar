Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
From iris.proofmode Require Import environments.

Ltac zesu_saturate_alignment :=
  match goal with
  | H : bv_extract 0 _ _ = _ |- _ => bv_saturate
  | H : Z.land (bv_unsigned _) _ = _ |- _ => bv_saturate
  end.

Ltac zesu_finish_little_endian :=
  match goal with
  | |- context[Z_to_little_endian _ _ _] =>
      rewrite /Z_to_little_endian /=;
      rewrite !Z.land_ones; [|lia..];
      rewrite !Z.shiftr_div_pow2; [|lia..];
      repeat eexists; repeat split; reflexivity
  end.

Ltac zesu_finish :=
  prepare_sidecond;
  try assumption;
  try zesu_saturate_alignment;
  try bv_solve;
  try lia;
  try zesu_finish_little_endian.

Ltac zesu_run :=
  unshelve liARun;
  zesu_finish.

Ltac zesu_block :=
  iStartProof;
  simpl;
  zesu_run.

Ltac zesu_tuple_witness T :=
  lazymatch T with
  | li_prod ?A ?B =>
      let head := open_constr:(_ : A) in
      let tail := zesu_tuple_witness B in constr:(li_pair head tail)
  | unit => constr:(tt)
  end.

Ltac zesu_instantiate_tuple :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      let witness := zesu_tuple_witness T in iExists witness
  end.

Ltac zesu_handoff := zesu_instantiate_tuple; zesu_run.

Ltac zesu_frame_handoff := timeout 5 (iFrame "∗"; zesu_run).

Tactic Notation "zesu_pack" constr(witness) :=
  iExists witness;
  iFrame;
  try done;
  try zesu_finish.
