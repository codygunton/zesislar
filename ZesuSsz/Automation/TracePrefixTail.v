(* Matching event prefixes determine a call's trace tail. *)
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.StackArrayIndices.
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

Lemma zesu_scons_event_mono left_event right_event (left right : spec) :
  left_event = right_event -> left ⊆ right ->
  scons left_event left ⊆ scons right_event right.
Proof. intros ->. apply zesu_scons_mono. Qed.

Lemma zesu_scons_snap_plain_event_mono left_event right_event accept (left right : spec) :
  left_event = right_event -> left ⊆ right ->
  scons_snap left_event accept left ⊆ scons right_event right.
Proof. intros ->. apply zesu_scons_snap_plain_mono. Qed.

Lemma zesu_scons_snap_event_mono left_event right_event accept predicate (left right : spec) :
  left_event = right_event ->
  (forall snapshot, accept snapshot -> predicate snapshot) -> left ⊆ right ->
  scons_snap left_event accept left ⊆ scons_snap right_event predicate right.
Proof. intros ->. apply zesu_scons_snap_mono. Qed.

Ltac zesu_trace_event_equal :=
  first [reflexivity | bv_solve |
    progress (repeat match goal with
      | H : @eq (bv _) _ _ |- _ => progress subst
      end); zesu_trace_event_equal |
    progress f_equal; zesu_trace_event_equal].

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
              zesu_matching_trace_tail candidate rest tail
          end
      | scons_snap ?event ?accept ?rest =>
          let declared := zesu_trace_prefix_head declared in
          lazymatch declared with
          | scons_snap ?expected ?predicate ?tail =>
              zesu_matching_trace_tail candidate rest tail
          | scons ?expected ?tail =>
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
        apply zesu_scons_event_mono;
        [zesu_trace_event_equal | zesu_trace_prefix_inclusion]
    | |- scons_snap _ _ _ ⊆ scons _ _ =>
        apply zesu_scons_snap_plain_event_mono;
        [zesu_trace_event_equal | zesu_trace_prefix_inclusion]
    | |- scons_snap _ _ _ ⊆ scons_snap _ _ _ =>
        apply zesu_scons_snap_event_mono;
        [zesu_trace_event_equal
        | solve [intros; assumption |
           let snapshot := fresh "snapshot" in
           let Hsnapshot := fresh "Hsnapshot" in
           intros snapshot Hsnapshot;
           lazymatch goal with
           | Hsnapshot : ?read = Some ?payload |- ?expected_read = Some ?expected =>
               let Hread := fresh "Hread" in
               assert (Hread : read = expected_read) by zesu_trace_event_equal;
               let Hequal := fresh "Hpayload" in
               assert (Hequal : payload = expected) by
                 (autounfold with zesu_selectors;
                  zesu_normalize_stack_array_indices; reflexivity);
               try rewrite <- Hread; try rewrite <- Hequal; exact Hsnapshot
           end]
         | zesu_trace_prefix_inclusion]
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
