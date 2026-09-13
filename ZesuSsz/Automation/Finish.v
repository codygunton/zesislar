Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Export ZesuSsz.Automation.Hooks.
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

Ltac zesu_finish_framed_wand :=
  lazymatch goal with
  | |- envs_entails _ ((?available -∗ ?requested) ∗ True)%I =>
      let Hpost := lazymatch goal with
        | |- envs_entails (Envs _ _ ?counter) _ => constr:(IAnon counter)
        end in
      iSplit;
      [iIntros "?"; rewrite ?Z_to_bv_bv_unsigned;
       timeout 5 (iFrame "∗");
       iEval (rewrite !bi.sep_True) in Hpost; iExact Hpost | done]
  end.

Ltac zesu_run :=
  unshelve (time "zesu_run" repeat zesu_liAStep; liShow);
  try zesu_finish_framed_wand;
  zesu_finish.

Ltac zesu_block :=
  iStartProof;
  simpl;
  zesu_run.

Ltac zesu_run_until boundary :=
  first [boundary tt |
    first [liUnfoldLate | zesu_liAStep]; zesu_run_until boundary | idtac].

Ltac zesu_known_array_values :=
  repeat match goal with
  | Hread : ?bytes !! ?index = Some ?value,
    Hknown : ?bytes !! ?known_index = Some ?known_value |- _ =>
      is_var value;
      tryif constr_eq value known_value then fail 1 else idtac;
      let Hindex := fresh "Hindex" in
      assert (Hindex : index = known_index) by
        (unLET; autorewrite with zesu_indices;
         rewrite ?Z.div_1_r; reflexivity);
      rewrite Hindex Hknown in Hread;
      injection Hread as Hread; subst value
  end.

Ltac zesu_finish_array_branch :=
  unLET; zesu_known_array_values; exfalso;
  first [bv_solve | match goal with
    | Hbranch : _ <> _ |- _ => bv_simplify Hbranch; congruence
    end | match goal with
    | Htag : ?tag <> _, Hbranch : bv_zero_extend _ ?tag = _ |- _ =>
        bv_simplify Htag; bv_simplify Hbranch; lia
    end].

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
