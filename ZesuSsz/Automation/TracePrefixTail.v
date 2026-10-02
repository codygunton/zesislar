(* Matching event prefixes determine a call's trace tail. *)
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepTracePrefixTail : Prop := zesu_step_trace_prefix_tail : True.

Ltac zesu_matching_trace_tail candidate generated declared :=
  lazymatch generated with
      | candidate => constr:(declared)
      | scons ?event ?rest =>
          lazymatch declared with
          | scons ?expected ?tail =>
              let _ := constr:(eq_refl : event = expected) in
              zesu_matching_trace_tail candidate rest tail
          end
      | scons_snap ?event ?accept ?rest =>
          lazymatch declared with
          | scons_snap ?expected ?predicate ?tail =>
              let _ := constr:(eq_refl : event = expected) in
              let _ := constr:(eq_refl : accept = predicate) in
              zesu_matching_trace_tail candidate rest tail
          end
      end.

Ltac zesu_close_matching_trace_tail :=
  let _ := constr:(_ : ZesuStepTracePrefixTail) in
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      let candidate := constr:(fun _ : list seq_label => False) in
      let opened := eval cbv beta iota delta [li_fst] in (body (candidate, tt)ₗ) in
      lazymatch opened with
      | (⌜?generated ⊆ ?declared⌝ ∗ ?bundle)%I =>
          lazymatch bundle with
          | context[instr_pre _ _] =>
              let tail := zesu_matching_trace_tail candidate generated declared in
              iExists (tail, tt)ₗ;
              iSplit; [iPureIntro; reflexivity |]
          end
      end
  end.
