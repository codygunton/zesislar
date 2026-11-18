From iris.proofmode Require Import environments.
From lithium Require Import pure_definitions.
Open Scope Z_scope.
(* Keep pure library heads out of implicit typeclass and simplification work.
   Explicit library rewrites and unfolding remain available. *)
Global Typeclasses Opaque scons scons_snap sapp read_mem write_mem
  bv_to_little_endian little_endian_to_bv Z_to_little_endian little_endian_to_Z.
Global Arguments scons _ _ : simpl never.
Global Arguments scons_snap _ _ _ : simpl never.
Global Arguments sapp _ _ : simpl never.
Global Arguments read_mem _ _ _ : simpl never.
Global Arguments write_mem _ _ _ _ : simpl never.
Global Arguments bv_to_little_endian _ _ _ : simpl never.
Global Arguments little_endian_to_bv _ _ : simpl never.
Global Arguments Z_to_little_endian _ _ _ : simpl never.
Global Arguments little_endian_to_Z _ _ : simpl never.

Ltac zesu_close_trace_inclusion ::=
  with_strategy opaque [scons scons_snap sapp]
    (iPureIntro; exact (ZesuSsz.Automation.TraceTailLemmas.zesu_scons_snap_subseteq_scons _ _ _)).

Ltac zesu_open_trace_exist ::=
  with_strategy opaque [scons scons_snap sapp]
  (lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      match goal with
      | |- context [scons _ ?tail] =>
          iExists (tail, tt)ₗ;
          try (iSplit; [zesu_close_trace_inclusion |])
      end
  end).

Ltac zesu_finish_trace_tail ::=
  with_strategy opaque [scons scons_snap sapp]
  (lazymatch goal with
  | |- scons_snap ?event _ ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (ZesuSsz.Automation.TraceTailLemmas.zesu_scons_snap_subseteq_scons _ _ _)
  | |- scons ?event ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (ZesuSsz.Automation.TraceTailLemmas.zesu_scons_subseteq_scons _ _)
  end).
