Require ZesuSsz.Automation.Hooks.
Require isla.automation.
Require Import ZesuSsz.Automation2.ResourceGroups.
From iris.proofmode Require Import intro_patterns.
Require Import ZesuSsz.Automation2.ContextRange.
Require Import ZesuSsz.Automation2.ArrayByteValues.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.ResidualLemmas.
From Coq Require Import Lia.
Require Coq.ZArith.Zbitwise.
From iris.proofmode Require Import tactics environments.
From Coq Require Import Bool.Bool.
From stdpp Require Import decidable.
From stdpp.bitvector Require Import definitions.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Select constrained values through source propositions, with correlated
   alternatives. Pure completion introduces no new arithmetic premise. *)

Ltac zesu_source_signed_lookup :=
  lazymatch goal with
  | |- (bv_signed (bv_sign_extend ?wide (bv_sign_extend ?middle ?byte)) < bv_signed ?zero)%Z =>
    assert_fails (has_evar byte);
    ZesuSsz.Automation2.VmClosed.zesu_closed_term wide; ZesuSsz.Automation2.VmClosed.zesu_closed_term middle;
    multimatch goal with
    | Hsource : (bv_signed (bv_sign_extend wide (bv_sign_extend middle ?loaded)) < bv_signed zero)%Z |- _ =>
      let equality := fresh "HsourceLoadedByte" in
      assert (equality : loaded = byte) by
        ArrayByteValues.zesu_finish_array_byte_lookup_if_closed;
      let transported := fresh "HsourceSignedByte" in
      pose proof Hsource as transported;
      rewrite equality in transported;
      exact transported
    end
  end.





Ltac zesu_source_signed_lookup_lower :=
 lazymatch goal with
 | |- (?threshold <= bv_unsigned ?byte)%Z =>
   assert_fails (has_evar byte);
   multimatch goal with
   | Hsource : (bv_signed (bv_sign_extend ?wide (bv_sign_extend ?middle ?loaded)) < bv_signed ?zero)%Z |- _ =>
     let transported := fresh "HsignedLookupLower" in
     assert (transported : (bv_signed (bv_sign_extend wide (bv_sign_extend middle byte)) < bv_signed zero)%Z) by
       zesu_source_signed_lookup;
     BitvectorFacts.zesu_source_signed_lower
   end
 end.





(* Retained order facts can use either standard integer presentation. *)
Ltac zesu_source_retained_order :=
  first [
    lazymatch goal with
    | |- Z.ge (bv_unsigned ?left) (bv_unsigned ?right) =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        multimatch goal with
        | retained : not (Z.lt (bv_signed (bv_zero_extend 128 left))
                         (bv_signed (bv_zero_extend 128 right))) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.nlt_ge in view;
            apply Z.le_ge; exact view
        | retained : Z.ge (bv_signed (bv_zero_extend 128 left))
                          (bv_signed (bv_zero_extend 128 right)) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            exact view
        end
    | |- Z.le (bv_unsigned ?right) (bv_unsigned ?left) =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        multimatch goal with
        | retained : not (Z.lt (bv_signed (bv_zero_extend 128 left))
                         (bv_signed (bv_zero_extend 128 right))) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.nlt_ge in view; exact view
        | retained : Z.ge (bv_signed (bv_zero_extend 128 left))
                          (bv_signed (bv_zero_extend 128 right)) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.ge_le; exact view
        end
    end |
    lazymatch goal with
    | |- Z.ge ?left ?right =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        apply Z.le_ge; assumption
    | |- Z.le ?left ?right =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        apply Z.ge_le; assumption
    end ].

(* A fact that reads a byte through `nth`, with the lookup of the same list
   and index in the context, is a fact about the lookup value. A strict upper
   bound `bound > value` becomes `value <= bound - 1` for the bound closers. *)
Ltac zesu_source_array_byte_nth close :=
  ArrayByteValues.zesu_rewrite_array_byte_nth_if_closed;
  first [close tt |
    lazymatch goal with
    | |- Z.gt ?bound ?value =>
        VmClosed.zesu_vm_closed bound;
        let ceiling := VmClosed.zesu_vm_eval_closed (Z.pred bound) in
        apply Z.lt_gt; apply (Z.le_lt_trans value ceiling bound);
        [close tt | VmClosed.zesu_vm_closed_decide]
    end].

Ltac zesu_source_fact := first [solve [assumption] | solve [reflexivity] |
 solve [zesu_source_retained_order] |
  lazymatch goal with
  | |- context [bv_unsigned (Z_to_bv ?width ?value)] =>
      assert_fails (has_evar value);
      let range := fresh "HsourceCastRange" in
      assert (range : (0 <= value < bv_modulus width)%Z) by
        ContextRange.zesu_hypothesis_cast_range_fact width value;
      rewrite (Z_to_bv_small width value range); clear range;
      zesu_source_fact
  end |
  solve [BitvectorFacts.zesu_source_unsigned_bound] |
  solve [BitvectorFacts.zesu_source_signed_lower] |
  solve [zesu_source_signed_lookup_lower] |
  solve [zesu_source_signed_lookup] |
  solve [zesu_source_array_byte_nth ltac:(fun _ => zesu_source_fact)] |
  solve [BitvectorFacts.zesu_source_signed_upper] | lazymatch goal with
| |- Z.ge (@bv_unsigned ?width ?value) Z0 =>
    apply Z.le_ge; exact (proj1 (bv_unsigned_in_range width value))
| |- Z.ge (@bv_unsigned ?width ?value) (@bv_unsigned ?closedWidth ?closedValue) =>
    assert_fails (has_evar closedValue);
    VmClosed.zesu_vm_closed closedValue;
    let reduced := eval cbv in (@bv_unsigned closedWidth closedValue) in
    constr_eq reduced Z0;
    apply Z.le_ge; change (Z.le reduced (@bv_unsigned width value));
    zesu_source_fact
| |- Z.le (@bv_unsigned ?closedWidth ?closedValue) (@bv_unsigned ?width ?value) =>
    assert_fails (has_evar closedValue);
    VmClosed.zesu_vm_closed closedValue;
    let reduced := eval cbv in (@bv_unsigned closedWidth closedValue) in
    constr_eq reduced Z0;
    change (Z.le reduced (@bv_unsigned width value));
    zesu_source_fact
end
 | lazymatch goal with
| |- Z.le ?value ?bound =>
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed bound;
    let normalized := eval cbv in bound in
    assert_fails (constr_eq bound normalized);
    change (Z.le value normalized); zesu_source_fact
| |- Z.lt ?value ?bound =>
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed bound;
    let normalized := eval cbv in bound in
    assert_fails (constr_eq bound normalized);
    change (Z.lt value normalized); zesu_source_fact
end
 | lazymatch goal with
| |- Z.le (bv_unsigned (bv_and ?value ?mask)) ?bound =>
    assert_fails (has_evar mask);
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed mask;
    VmClosed.zesu_vm_closed bound;
    let Hbound := fresh "HclosedMaskBound" in
    assert (Hbound : (bv_unsigned mask <= bound)%Z) by
      (vm_compute; congruence);
    rewrite bv_and_unsigned; rewrite Z.land_comm;
    let Hremaining := fresh "HmaskRemainder" in
    assert (Hremaining :
      (0 <= bv_unsigned mask - Z.land (bv_unsigned mask) (bv_unsigned value))%Z) by
      (rewrite Coq.ZArith.Zbitwise.Z.sub_land_same_l; apply Z.land_nonneg;
       left; exact (proj1 (bv_unsigned_in_range _ mask)));
    clear -Hbound Hremaining; lia
| |- Z.lt (bv_unsigned (bv_and ?value ?mask)) ?bound =>
    assert_fails (has_evar mask);
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed mask;
    VmClosed.zesu_vm_closed bound;
    let Hbound := fresh "HclosedMaskBound" in
    assert (Hbound : (bv_unsigned mask < bound)%Z) by
      (vm_compute; congruence);
    rewrite bv_and_unsigned; rewrite Z.land_comm;
    let Hremaining := fresh "HmaskRemainder" in
    assert (Hremaining :
      (0 <= bv_unsigned mask - Z.land (bv_unsigned mask) (bv_unsigned value))%Z) by
      (rewrite Coq.ZArith.Zbitwise.Z.sub_land_same_l; apply Z.land_nonneg;
       left; exact (proj1 (bv_unsigned_in_range _ mask)));
    clear -Hbound Hremaining; lia
end
 | lazymatch goal with | |- bool_decide ?fact = true => apply bool_decide_eq_true_2; zesu_source_fact | |- bool_decide ?fact = false => apply bool_decide_eq_false_2; zesu_source_fact | |- negb ?b = true => apply Bool.negb_true_iff; zesu_source_fact | |- ?a /\ ?b => split; zesu_source_fact | |- Z.le Z0 (@bv_unsigned ?width ?value) => assert_fails (has_evar value); exact (proj1 (bv_unsigned_in_range width value)) | |- Z.lt (@bv_unsigned ?width ?value) ?bound => assert_fails (has_evar value); assert_fails (has_evar bound); exact (proj2 (bv_unsigned_in_range width value)) | |- ?fact => let exposed := eval hnf in fact in lazymatch exposed with | ?left /\ ?right => change exposed; split; zesu_source_fact end end |
  (* A fact that no source closer proves, such as a merge-point meaning fact,
     gets the block's residual lemmas before the package fails. Without this,
     a failed fixed-fact check saturates the whole context and retries. *)
  ZesuSsz.Automation2.ResidualLemmas.zesu_residual_lemma].

Ltac zesu_source_finish_package :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_pure _ _) =>
      iPureIntro; zesu_source_fact
  | |- environments.envs_entails _ (@bi_sep _ _ _) =>
      iSplit; zesu_source_finish_package
  | |- environments.envs_entails _ (@big_opL _ (@bi_sep _) _ _ _ nil) =>
      rewrite big_sepL_nil; iEmpIntro
  | |- environments.envs_entails _ (@bi_emp _) => iEmpIntro
  end.

(* Occurrences of [target] in [term]. Subterms without an open evar count
   zero; an open evar inside an unsupported term former refuses. *)
Ltac2 rec zesu_source_evar_occurrences (target : evar) (term : constr) :=
  if Constr.has_evar term then
    let sum := fun (start : int) (terms : constr array) =>
      Array.fold_left (fun count item =>
        Int.add count (zesu_source_evar_occurrences target item)) start terms in
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Evar found arguments =>
        sum (if Evar.equal found target then 1 else 0) arguments
    | Constr.Unsafe.App head arguments =>
        sum (zesu_source_evar_occurrences target head) arguments
    | Constr.Unsafe.Cast body _ ty => sum 0 [|body; ty|]
    | Constr.Unsafe.Prod binder body => sum 0 [|Constr.Binder.type binder; body|]
    | Constr.Unsafe.Lambda binder body => sum 0 [|Constr.Binder.type binder; body|]
    | Constr.Unsafe.LetIn binder value body =>
        sum 0 [|Constr.Binder.type binder; value; body|]
    | Constr.Unsafe.Proj _ _ body => zesu_source_evar_occurrences target body
    | Constr.Unsafe.Case _ return_clause case_inversion scrutinee branches =>
        let (return_type, _) := return_clause in
        let start := sum (sum 0 [|return_type; scrutinee|]) branches in
        match case_inversion with
        | Constr.Unsafe.NoInvert => start
        | Constr.Unsafe.CaseInvert indices => sum start indices
        end
    | _ => Control.zero (Tactic_failure None)
    end
  else 0.

Ltac2 rec zesu_source_open_evars (found : evar list) (term : constr) :=
  if Constr.has_evar term then
    let collect := fun (start : evar list) (terms : constr array) =>
      Array.fold_left zesu_source_open_evars start terms in
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Evar candidate_evar arguments =>
        let known := List.exist (Evar.equal candidate_evar) found in
        collect (if known then found else candidate_evar :: found) arguments
    | Constr.Unsafe.App head arguments => collect (zesu_source_open_evars found head) arguments
    | Constr.Unsafe.Cast body _ ty => collect found [|body; ty|]
    | Constr.Unsafe.Prod binder body => collect found [|Constr.Binder.type binder; body|]
    | Constr.Unsafe.Lambda binder body => collect found [|Constr.Binder.type binder; body|]
    | Constr.Unsafe.LetIn binder value body =>
        collect found [|Constr.Binder.type binder; value; body|]
    | Constr.Unsafe.Proj _ _ body => zesu_source_open_evars found body
    | _ => Control.zero (Tactic_failure None)
    end
  else found.

Ltac2 zesu_source_mentions (evars : evar list) (term : constr) :=
  List.exist (fun candidate_evar => Int.lt 0 (zesu_source_evar_occurrences candidate_evar term)) evars.

(* The leaf list is [@cons Prop leaf rest] ... [@nil Prop]. *)
Ltac2 rec zesu_source_leaf_items (leaves : constr) :=
  match Constr.Unsafe.kind leaves with
  | Constr.Unsafe.App _ arguments =>
      if Int.equal (Array.length arguments) 3
      then Array.get arguments 1 :: zesu_source_leaf_items (Array.get arguments 2)
      else []
  | _ => []
  end.

Ltac2 rec zesu_source_leaf_list (items : constr list) :=
  match items with
  | [] => constr:(@nil Prop)
  | item :: rest =>
      Constr.Unsafe.make (Constr.Unsafe.App constr:(@cons)
        [|constr:(Prop); item; zesu_source_leaf_list rest|])
  end.

(* Number of leading [items] up to the last one that mentions [evars]. *)
Ltac2 rec zesu_source_last_mention (evars : evar list) (items : constr list) (index : int) (found : int) :=
  match items with
  | [] => found
  | item :: rest =>
      let index := Int.add index 1 in
      zesu_source_last_mention evars rest index
        (if zesu_source_mentions evars item then index else found)
  end.

Ltac2 rec zesu_source_grow_segment (segment : constr list) (evars : evar list) (remaining : constr list) :=
  let count := zesu_source_last_mention evars remaining 0 0 in
  if Int.equal count 0 then (segment, evars, remaining)
  else
    let taken := List.firstn count remaining in
    zesu_source_grow_segment (List.append segment taken)
      (List.fold_left zesu_source_open_evars evars taken) (List.skipn count remaining).

(* The leading segment of [leaves] is the shortest prefix that shares no open
   evar with the later leaves. It commits when none of its evars occurs in the
   goal outside the segment; otherwise, or when a term former is unsupported,
   every leaf stays in one uncommitted segment. *)
Ltac2 zesu_source_split_segment (leaves : constr) :=
  match zesu_source_leaf_items leaves with
  | [] => ([], [], true)
  | leading :: later =>
      let attempt := fun () =>
        let (segment, evars, remaining) :=
          zesu_source_grow_segment [leading] (zesu_source_open_evars [] leading) later in
        let goal := Control.goal () in
        let segment_local := List.for_all (fun candidate_evar =>
          Int.equal
            (List.fold_left (fun count item =>
              Int.add count (zesu_source_evar_occurrences candidate_evar item)) 0 segment)
            (zesu_source_evar_occurrences candidate_evar goal)) evars in
        if segment_local then (segment, remaining, true) else (leading :: later, [], false) in
      match Control.case attempt with
      | Val result => let (value, _) := result in value
      | Err _ => (leading :: later, [], false)
      end
  end.

Ltac zesu_source_with_segment leaves continuation :=
  let segment_split := ltac2:(leaves continuation |-
    let (segment, remaining, committed) :=
      zesu_source_split_segment (Option.get (Ltac1.to_constr leaves)) in
    Ltac1.apply continuation
      [Ltac1.of_constr (zesu_source_leaf_list segment);
       Ltac1.of_constr (zesu_source_leaf_list remaining);
       Ltac1.of_constr (if committed then constr:(true) else constr:(false))] Ltac1.run) in
  segment_split leaves continuation.

(* Each success unifies [requested] with one closed source proposition. The
   sort check matters only for a bare evar: unification with any other
   proposition already fixes the sort. *)
Ltac zesu_source_match_candidate requested :=
  multimatch goal with
  | source_fact : ?available |- _ =>
      tryif has_evar available then fail else idtac;
      tryif is_evar requested then
        (let available_sort := type of available in
         lazymatch available_sort with Prop => idtac
         | _ => fail 0 "The source candidate is not a proposition." end)
      else idtac;
      unify requested available
  end.

Ltac zesu_source_match_leaf requested :=
  tryif has_evar requested then zesu_source_match_candidate requested
  else
    let checked := fresh "HspatialConstraint" in
    assert (checked : requested) by
      (zesu_source_fact);
    clear checked.

Ltac zesu_source_match_leaves leaves :=
  lazymatch leaves with
  | @nil _ => idtac
  | @cons _ ?leaf ?rest => zesu_source_match_leaf leaf; zesu_source_match_leaves rest
  end.

(* A segment whose evars occur nowhere else in the goal keeps only its first
   solution: no later leaf can observe the choice, and every choice proves the
   same facts. Inside a segment, a shared evar keeps backtracking over
   candidates. [finish] must depend only on the goal. *)
Ltac zesu_source_match_segments leaves finish :=
  lazymatch leaves with
  | @nil _ => finish
  | _ =>
      zesu_source_with_segment leaves ltac:(fun segment rest committed =>
        lazymatch committed with
        | true => once (zesu_source_match_leaves segment);
            zesu_source_match_segments rest finish
        | false => zesu_source_match_leaves segment;
            zesu_source_match_segments rest finish
        end)
  end.

(* Requested facts in order: conjunctions split, Boolean decisions exposed. *)
Ltac zesu_source_fact_leaves requested leaves :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_fact_leaves fact leaves
  | bool_decide ?fact = false => zesu_source_fact_leaves (~ fact) leaves
  | negb (bool_decide ?fact) = true => zesu_source_fact_leaves (~ fact) leaves
  | negb (bool_decide ?fact) = false => zesu_source_fact_leaves fact leaves
  | ?left /\ ?right =>
      let later := zesu_source_fact_leaves right leaves in
      zesu_source_fact_leaves left later
  | _ => constr:(@cons Prop requested leaves)
  end.

Ltac zesu_source_tree_leaves requested leaves :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_fact_leaves fact leaves
  | @bi_sep _ ?left ?right =>
      let later := zesu_source_tree_leaves right leaves in
      zesu_source_tree_leaves left later
  | _ => leaves
  end.

Ltac zesu_source_match_fact requested finish :=
  let leaves := zesu_source_fact_leaves requested constr:(@nil Prop) in
  zesu_source_match_segments leaves finish.

Ltac zesu_source_match_tree requested finish :=
  let leaves := zesu_source_tree_leaves requested constr:(@nil Prop) in
  zesu_source_match_segments leaves finish.

(* Check fixed facts before any source-value alternatives can branch. *)
Ltac zesu_source_check_fixed_fact requested :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_check_fixed_fact fact
  | bool_decide ?fact = false => zesu_source_check_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = true => zesu_source_check_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = false => zesu_source_check_fixed_fact fact
  | ?left /\ ?right =>
      zesu_source_check_fixed_fact left; zesu_source_check_fixed_fact right
  | _ =>
      tryif has_evar requested then idtac
      else
        let checked := fresh "HsourceFixedConstraint" in
        tryif (assert (checked : requested) by zesu_source_fact)
        then clear checked
        else fail 0 "Unsupported fixed source fact:" requested
  end.

Ltac zesu_source_check_fixed_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_check_fixed_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_check_fixed_tree left; zesu_source_check_fixed_tree right
  | _ => idtac
  end.

(* The same walk, but a fixed fact that the source closers cannot prove does
   not stop the package. The residual tier gets one attempt. If it fails, the
   fact becomes its own goal on the shelf, and the package continues with the
   fact as a hypothesis. A fact with an evar is left to the matching step, so
   the witnesses are chosen as before. The caller must unshelve. *)
Ltac zesu_source_defer_fixed_fact requested :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_defer_fixed_fact fact
  | bool_decide ?fact = false => zesu_source_defer_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = true => zesu_source_defer_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = false => zesu_source_defer_fixed_fact fact
  | ?left /\ ?right =>
      zesu_source_defer_fixed_fact left; zesu_source_defer_fixed_fact right
  | _ =>
      tryif has_evar requested then idtac
      else
        let checked := fresh "HsourceFixedConstraint" in
        tryif (assert (checked : requested) by zesu_source_fact)
        then clear checked
        else
          let deferred := fresh "HdeferredFact" in
          first [assert (deferred : requested) by
                   ZesuSsz.Automation2.ResidualLemmas.zesu_residual_lemma
                | assert (deferred : requested); [shelve | ]]
  end.

Ltac zesu_source_defer_fixed_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_defer_fixed_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_defer_fixed_tree left; zesu_source_defer_fixed_tree right
  | _ => idtac
  end.

(* Traverse only the requested disjunction. Each registered leaf must close. *)
Ltac zesu_source_registered_disjunction_tree close :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_or _ _ _) =>
      first
        [ solve [iLeft; zesu_source_registered_disjunction_tree close]
        | solve [iRight; zesu_source_registered_disjunction_tree close] ]
  | |- environments.envs_entails _ (@bi_sep _ (@bi_or _ _ _) _) =>
      rewrite bi.sep_or_r;
      zesu_source_registered_disjunction_tree close
  | |- environments.envs_entails _ (@bi_sep _ ?target ?frame) =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence);
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source =>
          iApply (bi.sep_mono_l source frame target
            (@ZesuSsz.Automation.Hooks.zesu_pure_fact_intro _ target source evidence));
          try rewrite bi.sep_exist_r;
          solve [close]
      end
  | |- environments.envs_entails _ ?target =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence);
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source =>
          iApply (@ZesuSsz.Automation.Hooks.zesu_pure_fact_intro _ target source evidence);
          solve [close]
      end
  end.

(* A heterogeneous tuple retains the first path for each exact registered source. *)
Ltac zesu_source_candidate_contains candidates key :=
  lazymatch candidates with
  | tt => fail 0
  | ((?path, ?previous), ?rest) =>
      first [constr_eq_strict key previous | zesu_source_candidate_contains rest key]
  end.

Ltac zesu_source_candidate_append candidates candidate :=
  lazymatch candidates with
  | tt => constr:((candidate, tt))
  | (?head, ?rest) =>
      let tail := zesu_source_candidate_append rest candidate in
      constr:((head, tail))
  end.

Ltac zesu_source_candidate_key requested :=
  lazymatch requested with
  | @bi_sep _ ?target ?frame =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source => constr:((source ∗ frame)%I)
      end
  | ?target =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source => source
      end
  end.

Ltac zesu_source_collect_candidates requested path candidates continuation :=
  lazymatch requested with
  | @bi_or _ ?left ?right =>
      let left_path := eval cbv in (@List.app bool path (cons false nil)) in
      let right_path := eval cbv in (@List.app bool path (cons true nil)) in
      zesu_source_collect_candidates left left_path candidates
        ltac:(fun previous => zesu_source_collect_candidates right right_path previous continuation)
  | @bi_sep _ (@bi_or _ ?left ?right) ?frame =>
      let left_path := eval cbv in (@List.app bool path (cons false nil)) in
      let right_path := eval cbv in (@List.app bool path (cons true nil)) in
      let left_goal := constr:((left ∗ frame)%I) in
      let right_goal := constr:((right ∗ frame)%I) in
      zesu_source_collect_candidates left_goal left_path candidates
        ltac:(fun previous => zesu_source_collect_candidates right_goal right_path previous continuation)
  | _ =>
      tryif (let key := zesu_source_candidate_key requested in assert_fails (has_evar key))
      then
        let key := zesu_source_candidate_key requested in
        tryif zesu_source_candidate_contains candidates key
        then continuation candidates
        else let updated := zesu_source_candidate_append candidates constr:((path, key)) in
          continuation updated
      else continuation candidates
  end.

Ltac zesu_source_select_candidate_path path :=
  lazymatch path with
  | nil => idtac
  | cons ?direction ?rest =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_sep _ (@bi_or _ _ _) _) => rewrite bi.sep_or_r
      | _ => idtac
      end;
      lazymatch direction with false => iLeft | true => iRight end;
      zesu_source_select_candidate_path rest
  end.

Ltac zesu_source_try_candidates candidates close :=
  lazymatch candidates with
  | tt => fail 0
  | ((?path, ?key), ?rest) =>
      first [solve [zesu_source_select_candidate_path path;
                    zesu_source_registered_disjunction_tree close]
            | zesu_source_try_candidates rest close]
  end.

Ltac zesu_source_registered_disjunction close :=
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      lazymatch requested with
      | @bi_or _ _ _ => idtac
      | @bi_sep _ (@bi_or _ _ _) _ => idtac
      end;
      zesu_source_collect_candidates requested constr:(@nil bool) constr:(tt)
        ltac:(fun candidates => once (zesu_source_try_candidates candidates close))
  end.

Ltac zesu_source_registered_tree target :=
  lazymatch target with
  | @bi_or _ ?left ?right =>
      zesu_source_registered_tree left;
      zesu_source_registered_tree right
  | _ =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence)
  end.

Ltac zesu_source_open_registered_tree name body :=
  lazymatch body with
  | @bi_or _ ?left ?right =>
      let branch := iFresh in
      let pattern := constr:(IList (cons (cons (IIdent branch) nil)
        (cons (cons (IIdent branch) nil) nil))) in
      iDestruct name as pattern;
      [ zesu_source_open_registered_tree branch left
      | zesu_source_open_registered_tree branch right ]
  | _ =>
      let head := get_head body in
      let registration := constr:(_ : isla.automation.LithiumUnfold head) in
      iEval (unfold head) in name;
      repeat iDestruct name as (?) name;
      ResourceGroups.zesu_open_resource_groups
  end.

Ltac zesu_source_destruct_registered_disjunction :=
  iMatchHyp ltac:(fun name body =>
    let head := get_head body in
    constr_eq_strict head constr:(@bi_or);
    zesu_source_registered_tree body;
    zesu_source_open_registered_tree name body).
