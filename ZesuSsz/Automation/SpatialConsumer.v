Require Import ZesuSsz.Automation.All.
Require Import lithium.interpreter lithium.pure_definitions.
Require Import ZesuSsz.Automation.JoinEntailment.
Require Import ZesuSsz.Automation.VmClosed.
From iris.proofmode Require Import tactics environments.
From Coq Require Import Bool.Bool ZArith.
From stdpp Require Import decidable bitvector.tactics.
Local Open Scope Z_scope.

(* Reduce only the closed mask and result.  Preserve the symbolic word. *)
Ltac zesu_spatial_mask_fact :=
  lazymatch goal with
  | |- bv_and ?word ?mask = ?result =>
      assert_fails (has_evar word);
      VmClosed.zesu_vm_closed mask;
      VmClosed.zesu_vm_closed result;
      let mask_value := eval vm_compute in (bv_unsigned mask) in
      let result_value := eval vm_compute in (bv_unsigned result) in
      let Hmask := fresh "HspatialMaskValue" in
      let Hresult := fresh "HspatialResultValue" in
      assert (Hmask : bv_unsigned mask = mask_value) by (vm_compute; reflexivity);
      assert (Hresult : bv_unsigned result = result_value) by (vm_compute; reflexivity);
      apply bv_eq; rewrite bv_and_unsigned;
      rewrite Hmask; rewrite Hresult; assumption
  end.

(* The bias must be the closed half-modulus of a byte. *)
Ltac zesu_spatial_count_fact :=
  lazymatch goal with
  | |- bv_unsigned ?byte - ?bias < bv_unsigned ?length_word =>
      let byte_type := type of byte in constr_eq byte_type constr:(bv 8);
      assert_fails (has_evar byte);
      assert_fails (has_evar length_word);
      VmClosed.zesu_vm_closed bias;
      let actual := eval vm_compute in bias in
      let expected := eval vm_compute in (bv_half_modulus 8) in
      constr_eq actual expected;
      change (bv_unsigned byte - 128 < bv_unsigned length_word);
      multimatch goal with
      | Hlower : 128 <= bv_unsigned byte,
        Hguard : ~ bv_signed (bv_zero_extend 128 ?payload) >=
                   bv_signed (bv_zero_extend 128 length_word) |- _ =>
          let Hview := fresh "HspatialCountView" in
          pose proof Hguard as Hview;
          rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 _) in Hview;
          rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 _) in Hview;
          rewrite (JoinEntailment.zesu_join_mask_payload byte Hlower) in Hview;
          clear - Hview; Lia.lia
      end
  end.

(* These conversions use existing propositions.  They compute no symbolic term. *)
Ltac zesu_spatial_finish_fact :=
  first [solve [assumption] | solve [reflexivity] |
    solve [zesu_spatial_mask_fact] | solve [zesu_spatial_count_fact] |
    lazymatch goal with
    | |- bool_decide ?fact = true =>
        apply bool_decide_eq_true_2; zesu_spatial_finish_fact
    | |- bool_decide ?fact = false =>
        apply bool_decide_eq_false_2; zesu_spatial_finish_fact
    | |- negb ?boolean = true =>
        apply Bool.negb_true_iff; zesu_spatial_finish_fact
    | |- negb ?boolean = false =>
        apply Bool.negb_false_iff; zesu_spatial_finish_fact
    | |- ?left /\ ?right => split; zesu_spatial_finish_fact
    end].

Ltac zesu_spatial_finish_package :=
  first [solve [iFrame] |
    lazymatch goal with
    | |- environments.envs_entails _ (@bi_pure _ _) =>
        iPureIntro; zesu_spatial_finish_fact
    | |- environments.envs_entails _ (@bi_sep _ _ _) =>
        iSplit; zesu_spatial_finish_package
    end].

(* Keep matching alternatives alive until the complete package closes.  A
   concrete source proposition selects a value.  A type alone never selects it. *)
Ltac zesu_spatial_match_fact requested finish :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_spatial_match_fact fact finish
  | bool_decide ?fact = false => zesu_spatial_match_fact (~ fact) finish
  | negb (bool_decide ?fact) = true => zesu_spatial_match_fact (~ fact) finish
  | negb (bool_decide ?fact) = false => zesu_spatial_match_fact fact finish
  | ?left /\ ?right =>
      zesu_spatial_match_fact left
        ltac:(zesu_spatial_match_fact right finish)
  | _ =>
      tryif has_evar requested then
        multimatch goal with
        | source_fact : ?available |- _ =>
            assert_fails (has_evar available);
            unify requested available;
            finish
        end
      else
        let checked := fresh "HspatialConstraint" in
        assert (checked : requested) by
          (zesu_spatial_finish_fact);
        clear checked; finish
  end.

Ltac zesu_spatial_match_tree requested finish :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_spatial_match_fact fact finish
  | @bi_sep _ ?left ?right =>
      zesu_spatial_match_tree left
        ltac:(zesu_spatial_match_tree right finish)
  | _ => finish
  end.

(* Compare syntax without unifying the candidate with a pattern hole. *)
Ltac zesu_spatial_occurs candidate expression :=
  multimatch expression with
  | context [ ?part ] => constr_eq_strict candidate part
  end.

Ltac zesu_spatial_default_unused_bv candidate :=
  let bare := eval cbv beta iota zeta in candidate in
  is_evar bare;
  let T := type of bare in
  lazymatch T with
  | bv ?width =>
      lazymatch goal with |- ?remaining =>
        assert_fails (zesu_spatial_occurs bare remaining)
      end;
      assert_fails (
        multimatch goal with
        | local := ?value : ?T |- _ =>
            first [zesu_spatial_occurs bare value |
                   zesu_spatial_occurs bare T]
        | local : ?T |- _ => zesu_spatial_occurs bare T
        end);
      unify bare (Z_to_bv width 0)
  end.

Ltac zesu_spatial_fill_unused witnesses :=
  lazymatch witnesses with
  | @pair _ _ ?value ?tail =>
      zesu_spatial_fill_unused value; zesu_spatial_fill_unused tail
  | @li_pair _ _ ?value ?tail =>
      zesu_spatial_fill_unused value; zesu_spatial_fill_unused tail
  | tt => idtac
  | _ => try zesu_spatial_default_unused_bv witnesses
  end.

(* Retain every introduced witness so unused slots cannot escape as shelves. *)
Ltac zesu_spatial_open_witnesses fuel continuation :=
  lazymatch fuel with
  | S ?remaining =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
          assert_fails (has_evar T);
          let witness := Hooks.zesu_constraint_witness T in
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod;
          zesu_spatial_open_witnesses remaining ltac:(fun rest =>
            let tracked := constr:((witness, rest)) in continuation tracked)
      | |- environments.envs_entails _ ?requested =>
          continuation constr:(tt)
      end
  | O => fail 0 "The package exceeds the existential step limit."
  end.

Ltac zesu_spatial_pack_package finish :=
  zesu_expose_environment_alias;
  zesu_spatial_open_witnesses constr:(64%nat) ltac:(fun witnesses =>
    lazymatch goal with
    | |- environments.envs_entails _ ?requested =>
        zesu_spatial_match_tree requested ltac:(
          zesu_spatial_fill_unused witnesses;
          solve [cut True;
            [intro; finish |
             assert_fails (has_evar witnesses); exact I]])
    end).

Ltac zesu_spatial_consumer lemma finish :=
  iApply lemma;
  zesu_spatial_pack_package finish.
