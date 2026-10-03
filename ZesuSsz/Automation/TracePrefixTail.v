(* Matching event prefixes determine a call's trace tail. *)
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.Hooks.
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

Ltac zesu_trace_tail_continuation bundle :=
  lazymatch bundle with
  | context[instr_pre _ _] => idtac
  | LET_ID ?body ?argument =>
      let opened := eval cbv beta in (body argument) in
      zesu_trace_tail_continuation opened
  | _ =>
      let head := get_head bundle in
      is_var head;
      let opened := eval unfold head in bundle in
      zesu_trace_tail_continuation opened
  end.

Ltac zesu_close_matching_trace_tail :=
  let _ := constr:(_ : ZesuStepTracePrefixTail) in
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      let candidate := constr:(fun _ : list seq_label => False) in
      let opened := eval cbv beta iota delta [li_fst] in (body (candidate, tt)ₗ) in
      lazymatch opened with
      | (⌜?generated ⊆ ?declared⌝ ∗ ?bundle)%I =>
          zesu_trace_tail_continuation bundle;
          let tail := zesu_matching_trace_tail candidate generated declared in
          iExists (tail, tt)ₗ;
          iSplit; [iPureIntro; zesu_trace_prefix_inclusion |]
      end
  end.

Ltac zesu_require_owned_trace_array address bytes :=
  assert_fails (has_evar address);
  assert_fails (has_evar bytes);
  iMatchHyp ltac:(fun Howned resource =>
    lazymatch resource with (?actual ↦ₘ∗ ?owned)%I =>
      assert_fails (has_evar actual);
      assert_fails (has_evar owned);
      unify actual address;
      unify owned bytes
    end).

Ltac zesu_select_owned_trace_memory_witness :=
  let _ := constr:(_ : ZesuStepTracePrefixTail) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (list (bv 8)) ?body) =>
    iMatchHyp ltac:(fun Htrace resource =>
      lazymatch resource with spec_trace ?trace =>
        lazymatch trace with ?events ?data ?size ?payload ?tail =>
          lazymatch type of payload with list (bv 8) => idtac end;
          lazymatch type of data with bv 64 => idtac end;
          let opened := eval cbv beta iota in (body payload) in
          lazymatch opened with @bi_exist _ spec ?continuation =>
            let selected := eval cbv beta iota in (continuation tail) in
            lazymatch selected with ((?address ↦ₘ∗ ?bytes) ∗ ?rest)%I =>
              unify bytes payload;
              zesu_require_owned_trace_array (bv_unsigned data) payload;
              lazymatch rest with context[spec_trace ?expected] =>
                lazymatch expected with ?expectedEvents ?expectedData ?expectedSize ?expectedPayload ?expectedTail =>
                  constr_eq events expectedEvents;
                  unify expectedSize size;
                  unify expectedPayload payload;
                  unify expectedTail tail;
                  let Hdata := fresh "HtraceData" in
                  assert (Hdata : expectedData = data) by
                    (timeout 2 (first [reflexivity | assumption | bv_solve]));
                  let Haddress := fresh "HtraceAddress" in
                  assert (Haddress : address = bv_unsigned data) by
                    (timeout 2 (first [reflexivity | assumption | rewrite Hdata; reflexivity]));
                  iExists payload; iExists tail;
                  try rewrite Hdata; try rewrite Haddress;
                  clear Hdata Haddress
                end
              end
            end
          end
        end
      end)
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod (list (bv 8)) unit)) ?body) =>
    iMatchHyp ltac:(fun Htrace resource =>
      lazymatch resource with spec_trace ?trace =>
        lazymatch trace with ?events ?data ?size ?payload ?tail =>
          lazymatch type of payload with list (bv 8) => idtac end;
          lazymatch type of data with bv 64 => idtac end;
          let witness := constr:((tail, payload, tt)ₗ) in
          let opened := eval cbv beta iota delta [li_fst] in (body witness) in
          lazymatch opened with ((?address ↦ₘ∗ ?bytes) ∗ ?rest)%I =>
            unify bytes payload;
            unify address (bv_unsigned data);
            zesu_require_owned_trace_array address payload;
            lazymatch rest with context[spec_trace ?expected] =>
              first [unify expected trace; iExists witness
              | lazymatch expected with ?expectedEvents ?expectedData ?expectedSize ?expectedPayload ?expectedTail =>
                  constr_eq events expectedEvents;
                  unify expectedSize size;
                  unify expectedPayload payload;
                  unify expectedTail tail;
                  let Hdata := fresh "HtraceData" in
                  assert (Hdata : expectedData = data) by
                    (timeout 2 (first [reflexivity | assumption | bv_solve]));
                  iExists witness;
                  rewrite Hdata; clear Hdata
                end]
            end
          end
        end
      end)
  | |- envs_entails _ (@bi_exist _ (li_prod (list (bv 8)) unit) ?body) =>
    iMatchHyp ltac:(fun Htrace resource =>
      lazymatch resource with spec_trace ?trace =>
        lazymatch trace with ?events ?data ?size ?payload ?tail =>
          lazymatch type of payload with list (bv 8) => idtac end;
          lazymatch type of data with bv 64 => idtac end;
          let witness := constr:((payload, tt)ₗ) in
          let opened := eval cbv beta iota delta [li_fst] in (body witness) in
          lazymatch opened with @bi_exist _ spec ?continuation =>
            let selected := eval cbv beta iota delta [li_fst] in (continuation tail) in
            lazymatch selected with ((?address ↦ₘ∗ ?bytes) ∗ ?rest)%I =>
              unify bytes payload;
              unify address (bv_unsigned data);
              zesu_require_owned_trace_array address payload;
              lazymatch rest with context[spec_trace ?expected] =>
                lazymatch expected with ?expectedEvents ?expectedData ?expectedSize ?expectedPayload ?expectedTail =>
                  constr_eq events expectedEvents;
                  unify expectedSize size;
                  unify expectedPayload payload;
                  unify expectedTail tail;
                  let Hdata := fresh "HtraceData" in
                  assert (Hdata : expectedData = data) by
                    (timeout 2 (first [reflexivity | assumption | bv_solve]));
                  iExists witness; iExists tail;
                  try rewrite Hdata; clear Hdata
                end
              end
            end
          end
        end
      end)
  end.
