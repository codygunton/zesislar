(* Matching event prefixes determine a call's trace tail. *)
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepTracePrefixTail : Prop := zesu_step_trace_prefix_tail : True.

Lemma zesu_scons_mono event (left right : spec) :
  left ⊆ right -> scons event left ⊆ scons event right.
Proof. unfold subseteq, spec_subseteq, scons. naive_solver. Qed.

Lemma zesu_scons_snap_plain_mono event accept (left right : spec) :
  left ⊆ right -> scons_snap event accept left ⊆ scons event right.
Proof. unfold subseteq, spec_subseteq, scons_snap, scons. naive_solver. Qed.

Lemma zesu_scons_snap_mono event accept predicate (left right : spec) :
  (forall snapshot, accept snapshot -> predicate snapshot) ->
  left ⊆ right -> scons_snap event accept left ⊆ scons_snap event predicate right.
Proof. unfold subseteq, spec_subseteq, scons_snap. naive_solver. Qed.

Ltac zesu_trace_prefix_head value :=
  lazymatch value with
  | scons _ _ => constr:(value)
  | scons_snap _ _ _ => constr:(value)
  | _ =>
      let head := get_head value in
      let expanded := eval unfold head in value in
      zesu_trace_prefix_head expanded
  end.

Ltac zesu_matching_trace_tail candidate generated declared :=
  lazymatch generated with
      | candidate => constr:(declared)
      | scons ?event ?rest =>
          let declared := zesu_trace_prefix_head declared in
          lazymatch declared with
          | scons ?expected ?tail =>
              let _ := constr:(eq_refl : event = expected) in
              zesu_matching_trace_tail candidate rest tail
          end
      | scons_snap ?event ?accept ?rest =>
          let declared := zesu_trace_prefix_head declared in
          lazymatch declared with
          | scons_snap ?expected ?predicate ?tail =>
              let _ := constr:(eq_refl : event = expected) in
              let _ := constr:(eq_refl : accept = predicate) in
              zesu_matching_trace_tail candidate rest tail
          | scons ?expected ?tail =>
              let _ := constr:(eq_refl : event = expected) in
              zesu_matching_trace_tail candidate rest tail
          end
      | _ =>
          let generated := zesu_trace_prefix_head generated in
          zesu_matching_trace_tail candidate generated declared
      end.

Ltac zesu_trace_prefix_inclusion :=
  first [reflexivity
  | lazymatch goal with
    | |- ?generated ⊆ ?declared =>
        let left := zesu_trace_prefix_head generated in
        let right := zesu_trace_prefix_head declared in
        change (left ⊆ right)
    end;
    lazymatch goal with
    | |- scons _ _ ⊆ scons _ _ =>
        apply zesu_scons_mono; zesu_trace_prefix_inclusion
    | |- scons_snap _ _ _ ⊆ scons _ _ =>
        apply zesu_scons_snap_plain_mono; zesu_trace_prefix_inclusion
    | |- scons_snap _ _ _ ⊆ scons_snap _ _ _ =>
        apply zesu_scons_snap_mono;
        [first [solve [intros; assumption] | idtac] | zesu_trace_prefix_inclusion]
    end].

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
              iSplit; [iPureIntro; zesu_trace_prefix_inclusion |]
          end
      end
  end.
