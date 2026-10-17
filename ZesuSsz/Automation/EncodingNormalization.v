Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Rewrites.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.EntryIntro.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Class ZesuStepEncodingNormalization : Prop := {}.

Lemma zesu_bv_signed_zero_extend_wide (n width : N) (value : bv n) :
  (n < width)%N ->
  bv_signed (bv_zero_extend width value) = bv_unsigned value.
Proof.
  intros Hwidth. rewrite bv_zero_extend_signed. apply bv_swrap_small.
  pose proof (bv_unsigned_in_range n value) as Hrange.
  assert (Hsuccessor : bv_half_modulus (N.succ n) = bv_modulus n).
  { unfold bv_half_modulus, bv_modulus.
    rewrite N2Z.inj_succ Z.pow_succ_r; last lia.
    rewrite Z.mul_comm Z.div_mul; lia. }
  pose proof (bv_half_modulus_le_mono (N.succ n) width ltac:(lia)) as Hmono.
  pose proof (bv_half_modulus_nonneg width).
  rewrite Hsuccessor in Hmono. lia.
Qed.
Print Assumptions zesu_bv_signed_zero_extend_wide.

(* The marker prevents a second split in either child, including later calls. *)
Inductive ZesuEncodingSplitUsed : Prop := zesu_encoding_split_used.

(* Applying this lemma abstracts only the goal. Existing hypotheses stay exact. *)
Lemma zesu_encoding_bool_case (condition : bool) (predicate : bool -> Prop) :
  (condition = true -> predicate true) ->
  (condition = false -> predicate false) -> predicate condition.
Proof.
  intros Htrue Hfalse. destruct condition.
  - apply Htrue. reflexivity.
  - apply Hfalse. reflexivity.
Qed.

(* Only the selected closed term enters the virtual machine. *)
Ltac zesu_encoding_width_literal width :=
  tryif is_var width then fail 0 else
  lazymatch width with
  | N0 => idtac
  | Npos ?positive => zesu_region_positive_literal positive
  end.

Ltac zesu_encoding_bv_literal value :=
  tryif is_var value then fail 0 else
  lazymatch value with
  | @BV ?width ?integer _ =>
      zesu_encoding_width_literal width; zesu_region_integer_literal integer
  | Z_to_bv ?width ?integer =>
      zesu_encoding_width_literal width; zesu_region_integer_literal integer
  end.

Ltac zesu_encoding_bit_literal value :=
  zesu_encoding_bv_literal value;
  lazymatch value with
  | @BV 1 ?integer _ => first [constr_eq integer 0%Z | constr_eq integer 1%Z]
  | Z_to_bv 1 ?integer => first [constr_eq integer 0%Z | constr_eq integer 1%Z]
  end.

Ltac zesu_encoding_change term reduced :=
  change_no_check term with reduced.

(* Read a local alias without changing its body or any hypothesis. *)
Ltac zesu_encoding_decision_body condition continuation :=
  assert_fails (zesu_condition_has_unresolved_evar condition);
  lazymatch condition with
  | @bool_decide _ _ => continuation condition
  | _ =>
      is_var condition;
      multimatch goal with
      | local := ?body |- _ =>
          constr_eq local condition;
          lazymatch body with @bool_decide _ _ => continuation body end
      end
  end.

(* Check facts without changing the goal or any hypothesis. *)
Ltac zesu_encoding_decision_known condition :=
  zesu_encoding_decision_body condition ltac:(fun decision =>
    lazymatch decision with
    | @bool_decide ?predicate ?instance =>
        first
          [multimatch goal with
           | H : ?statement |- _ => constr_eq statement constr:(condition = true)
           end
          |multimatch goal with
           | H : ?statement |- _ => constr_eq statement constr:(condition = false)
           end
          |multimatch goal with
           | H : ?statement |- _ => constr_eq statement predicate
           end
          |multimatch goal with
           | H : ~ ?statement |- _ => constr_eq statement predicate
           end]
    end).

(* A hypothesis must decide the exact predicate. No arithmetic search decides it. *)
Ltac zesu_encoding_ite_decision condition :=
  zesu_encoding_decision_body condition ltac:(fun decision =>
    lazymatch decision with
    | @bool_decide ?predicate ?instance =>
        first
          [multimatch goal with
           | H : ?statement |- _ =>
               constr_eq statement constr:(condition = true); rewrite H
           end
          |multimatch goal with
           | H : ?statement |- _ =>
               constr_eq statement constr:(condition = false); rewrite H
           end
          |multimatch goal with
           | H : ?statement |- _ =>
               constr_eq statement predicate;
               let Heq := fresh "HencodingDecision" in
               assert (Heq : condition = true) by
                 (change (decision = true); apply bool_decide_eq_true_2; exact H);
               rewrite Heq; clear Heq
           end
          |multimatch goal with
           | H : ~ ?statement |- _ =>
               constr_eq statement predicate;
               let Heq := fresh "HencodingDecision" in
               assert (Heq : condition = false) by
                 (change (decision = false); apply bool_decide_eq_false_2; exact H);
               rewrite Heq; clear Heq
           end]
    end).

Ltac zesu_encoding_ite_term term :=
  lazymatch term with
  | @ite _ true ?left _ => zesu_encoding_change term left
  | @ite _ false _ ?right => zesu_encoding_change term right
  | @ite _ ?condition _ _ => zesu_encoding_ite_decision condition
  end.

(* Preserve the threshold spelling until its Boolean has a branch value. *)
Ltac zesu_encoding_in_decision term :=
  idtac;
  multimatch goal with
  | |- context[@bool_decide ?predicate ?instance] =>
      lazymatch predicate with context[term] => idtac end
  end.

Ltac zesu_encoding_compute term :=
  assert_fails (zesu_encoding_in_decision term);
  zesu_stack_closed_term term;
  let reduced := eval vm_compute in term in
  tryif constr_eq term reduced then fail 0
  else zesu_encoding_change term reduced.

(* Rebuild the entire Boolean with its unsigned decision instance. *)
Ltac zesu_encoding_register_threshold condition :=
  assert_fails (zesu_condition_has_unresolved_evar condition);
  lazymatch condition with
  | @bool_decide
      (Z.lt (@bv_signed 128 (@bv_zero_extend 64 128 ?left))
            (@bv_signed 128 (@bv_zero_extend 64 128 (@BV 64 ?integer I)))) ?instance =>
      zesu_region_integer_literal integer;
      let right := constr:(@BV 64 integer I) in
      let target := constr:((bv_unsigned left < bv_unsigned right)%Z) in
      let Heq := fresh "HencodingThreshold" in
      assert (Heq : condition = bool_decide target) by
        (apply bool_decide_ext;
         rewrite (zesu_bv_signed_zero_extend_wide 64 128 left ltac:(lia));
         rewrite (zesu_bv_signed_zero_extend_wide 64 128 right ltac:(lia));
         reflexivity);
      rewrite Heq; clear Heq
  end.

Ltac zesu_encoding_wide_term term :=
  assert_fails (zesu_encoding_in_decision term);
  lazymatch term with
  | @bv_signed ?width (@bv_zero_extend ?n ?width ?value) =>
      let Hwidth := fresh "HencodingWidth" in
      assert (Hwidth : (n < width)%N) by lia;
      rewrite (zesu_bv_signed_zero_extend_wide n width value Hwidth);
      clear Hwidth
  end.

Ltac zesu_encoding_cast_term term :=
  assert_fails (zesu_encoding_in_decision term);
  lazymatch term with
  | @bv_unsigned ?width (Z_to_bv ?width ?value) =>
      assert_fails (zesu_condition_has_unresolved_evar width);
      assert_fails (zesu_condition_has_unresolved_evar value);
      zesu_encoding_width_literal width;
      let modulus := eval vm_compute in (bv_modulus width) in
      let Hbound := fresh "HencodingBound" in
      assert (Hbound : (0 <= value < modulus)%Z) by lia;
      rewrite (zesu_bv_unsigned_Z_to_bv_small width value Hbound);
      clear Hbound
  end.

Ltac zesu_encoding_literal_term term :=
  lazymatch term with
  | @bv_zero_extend 1 64 ?value =>
      zesu_encoding_bit_literal value; zesu_encoding_compute term
  | @bv_xor _ ?left ?right =>
      zesu_encoding_bv_literal left; zesu_encoding_bv_literal right;
      zesu_encoding_compute term
  | @bv_sub _ ?left ?right =>
      zesu_encoding_bv_literal left; zesu_encoding_bv_literal right;
      zesu_encoding_compute term
  | @bv_unsigned _ ?value =>
      zesu_encoding_bv_literal value; zesu_encoding_compute term
  end.

(* These steps change only the goal. They do not split any condition. *)
Ltac zesu_encoding_matching_term statement :=
  first
    [multimatch statement with
     | context[@bool_decide ?predicate ?instance] =>
         first [zesu_encoding_ite_decision constr:(@bool_decide predicate instance) |
                zesu_encoding_register_threshold constr:(@bool_decide predicate instance)]
     end
    |multimatch statement with
     | context[@ite ?type ?condition ?left ?right] =>
         zesu_encoding_ite_term constr:(@ite type condition left right)
     end
    |multimatch statement with
     | context[@bv_zero_extend 1 64 ?value] =>
         zesu_encoding_literal_term constr:(@bv_zero_extend 1 64 value)
     end
    |multimatch statement with
     | context[@bv_xor ?width ?left ?right] =>
         zesu_encoding_literal_term constr:(@bv_xor width left right)
     | context[@bv_sub ?width ?left ?right] =>
         zesu_encoding_literal_term constr:(@bv_sub width left right)
     end
    |multimatch statement with
     | context[@bv_unsigned ?width ?value] =>
         first [zesu_encoding_literal_term constr:(@bv_unsigned width value) |
                zesu_encoding_cast_term constr:(@bv_unsigned width value)]
     end
    |multimatch statement with
     | context[@bv_signed ?width (@bv_zero_extend ?n ?width ?value)] =>
         zesu_encoding_wide_term constr:(@bv_signed width (@bv_zero_extend n width value))
     end].

Ltac zesu_encoding_without_split :=
  repeat progress lazymatch goal with
  | |- ?statement => zesu_encoding_matching_term statement
  end.

(* A split requires the identical Boolean, including its decision instance,
   on both equality sides. A child can reduce terms but cannot split again. *)
Ltac zesu_encoding_shared_condition continuation :=
  lazymatch goal with
  | |- @eq _ ?left_side ?right_side =>
      multimatch left_side with
      | context[@bool_decide ?predicate ?instance] =>
          let condition := constr:(@bool_decide predicate instance) in
          assert_fails (zesu_condition_has_unresolved_evar condition);
          multimatch right_side with
          | context[@bool_decide ?other ?other_instance] =>
              constr_eq condition constr:(@bool_decide other other_instance);
              continuation condition
          end
      end
  end.

Ltac zesu_encoding_split_once :=
  lazymatch goal with
  | _ : ZesuEncodingSplitUsed |- _ => fail 0
  | _ =>
      zesu_encoding_shared_condition ltac:(fun condition =>
        assert_fails (zesu_encoding_decision_known condition);
        let Hused := fresh "HencodingSplitUsed" in
        assert (Hused : ZesuEncodingSplitUsed) by constructor;
        pattern condition;
        apply (zesu_encoding_bool_case condition);
        let Hcase := fresh "HencodingCase" in
        intro Hcase; cbv beta;
        zesu_encoding_without_split)
  end.

(* The source key and exact registered leaf survive one goal rewrite. *)
Inductive ZesuEncodingConditionalUsed {Sigma} (source : iProp Sigma)
    (facts : Prop) (entry : ZesuEntryIntro source facts) (leaf : Prop) : Prop :=
  ZesuEncodingConditionalWasUsed.

Ltac zesu_encoding_registered_entry Sigma source facts evidence :=
  assert_fails (has_evar source);
  assert_fails (has_evar facts);
  assert_fails (has_evar evidence);
  let registered := open_constr:(ltac:(ltac2:(zesu_unique_entry_registration ()))
    : @ZesuEntryIntro Sigma source _) in
  assert_fails (has_evar registered);
  let registeredType := type of registered in
  assert_fails (has_evar registeredType);
  lazymatch registeredType with
  | @ZesuEntryIntro _ _ ?registeredFacts =>
      constr_eq facts registeredFacts; constr_eq evidence registered
  end.

Ltac zesu_encoding_apply_conditional Sigma source facts evidence leaf premise leafProof :=
  assert_fails (idtac;
    match goal with
    | _ : @ZesuEncodingConditionalUsed Sigma source facts evidence leaf |- _ => idtac
    end);
  let premiseProof := constr:(ltac:(first
    [assumption
    |zesu_switch_enabled constr:(ZesuStepPureFactHints);
     let registered := zesu_registered_pure_fact premise in exact registered]) : premise) in
  rewrite (leafProof premiseProof);
  let used := fresh "HencodingConditionalUsed" in
  pose proof (@ZesuEncodingConditionalWasUsed Sigma source facts evidence leaf) as used.

Ltac2 Type zesu_encoding_conditional := [
  ZesuEncodingConditional
    (constr, constr, constr, constr, bool list, constr, constr, constr)
].
Ltac2 Type exn ::= [ ZesuEncodingConditionalAmbiguity (constr) ].

Ltac2 zesu_encoding_goal_contains (wanted : constr) :=
  Control.plus
    (fun () =>
      ltac1:(wanted |-
        lazymatch goal with |- context[wanted] => idtac end)
        (Ltac1.of_constr wanted);
      true)
    (fun _ => false).

(* Traverse only the fact bundle named by an applied entry registration. *)
Ltac2 rec zesu_encoding_conditional_leaves sigma source root evidence path facts :=
  lazy_match! facts with
  | ?first /\ ?second =>
      List.append
        (zesu_encoding_conditional_leaves sigma source root evidence
          (List.append path [true]) first)
        (zesu_encoding_conditional_leaves sigma source root evidence
          (List.append path [false]) second)
  | ?premise -> @eq ?a ?lhs
      (if @bool_decide ?predicate ?decision then ?yes else ?no) =>
      if zesu_encoding_goal_contains lhs then
        [ZesuEncodingConditional sigma source root evidence path facts premise lhs]
      else []
  | _ => []
  end.

Ltac2 zesu_encoding_same_conditional first second :=
  match first with
  | ZesuEncodingConditional sigma source facts evidence path _ _ _ =>
      match second with
      | ZesuEncodingConditional other_sigma other_source other_facts other_evidence other_path _ _ _ =>
          Bool.and (Constr.equal sigma other_sigma)
            (Bool.and (Constr.equal source other_source)
              (Bool.and (Constr.equal facts other_facts)
                (Bool.and (Constr.equal evidence other_evidence)
                  (List.equal Bool.equal path other_path))))
      end
  end.

Ltac2 zesu_encoding_conditional_lhs candidate :=
  match candidate with
  | ZesuEncodingConditional _ _ _ _ _ _ _ lhs => lhs
  end.

Ltac2 zesu_encoding_collect_conditionals () :=
  List.fold_left (fun found declaration =>
    let (_, _, statement) := declaration in
    lazy_match! statement with
    | @ZesuEntryIntroApplied ?sigma ?source ?facts ?evidence =>
        let leaves := zesu_encoding_conditional_leaves
          sigma source facts evidence [] facts in
        match leaves with
        | [] => found
        | _ =>
            ltac1:(sigma source facts evidence |-
              zesu_encoding_registered_entry sigma source facts evidence)
              (Ltac1.of_constr sigma) (Ltac1.of_constr source)
              (Ltac1.of_constr facts) (Ltac1.of_constr evidence);
            List.fold_left (fun unique candidate =>
              if List.exist (zesu_encoding_same_conditional candidate) unique
              then unique else List.append unique [candidate]) found leaves
        end
    | _ => found
    end) [] (Control.hyps ()).

(* Check all keys before premise search. A missing premise cannot hide ambiguity. *)
Ltac2 rec zesu_encoding_unique_conditionals candidates :=
  match candidates with
  | [] => ()
  | first :: remaining =>
      let lhs := zesu_encoding_conditional_lhs first in
      if List.exist (fun other =>
          Constr.equal lhs (zesu_encoding_conditional_lhs other)) remaining then
        Control.throw (ZesuEncodingConditionalAmbiguity lhs)
      else zesu_encoding_unique_conditionals remaining
  end.

Ltac2 rec zesu_encoding_project_owned proof path :=
  match path with
  | [] => proof
  | first :: remaining =>
      let next := if first then constr:(proj1 $proof) else constr:(proj2 $proof) in
      zesu_encoding_project_owned next remaining
  end.

Ltac2 zesu_encoding_owned_conditional facts leaf path :=
  match List.find_opt (fun declaration =>
      let (_, _, statement) := declaration in Constr.equal statement leaf)
      (Control.hyps ()) with
  | Some declaration => let (name, _, _) := declaration in Control.hyp name
  | None =>
      match List.find_opt (fun declaration =>
          let (_, _, statement) := declaration in Constr.equal statement facts)
          (Control.hyps ()) with
      | Some declaration =>
          let (name, _, _) := declaration in
          zesu_encoding_project_owned (Control.hyp name) path
      | None => Control.zero (Tactic_failure None)
      end
  end.

Ltac2 rec zesu_encoding_try_conditional candidates :=
  match candidates with
  | [] => Control.zero (Tactic_failure None)
  | candidate :: remaining =>
      Control.plus (fun () =>
        match candidate with
        | ZesuEncodingConditional sigma source facts evidence path leaf premise _ =>
            let proof := zesu_encoding_owned_conditional facts leaf path in
            ltac1:(sigma source facts evidence leaf premise proof |-
              assert_fails (has_evar leaf);
              zesu_encoding_apply_conditional sigma source facts evidence leaf premise proof)
              (Ltac1.of_constr sigma) (Ltac1.of_constr source)
              (Ltac1.of_constr facts) (Ltac1.of_constr evidence)
              (Ltac1.of_constr leaf) (Ltac1.of_constr premise) (Ltac1.of_constr proof)
        end)
        (fun _ => zesu_encoding_try_conditional remaining)
  end.

Ltac2 zesu_encoding_conditional_once () :=
  let candidates := zesu_encoding_collect_conditionals () in
  zesu_encoding_unique_conditionals candidates;
  zesu_encoding_try_conditional candidates.

Set Default Proof Mode "Classic".
Ltac zesu_encoding_conditional_once := ltac2:(zesu_encoding_conditional_once ()).

Ltac zesu_encoding_normalization_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEncodingNormalization);
  progress (try zesu_encoding_conditional_once;
    zesu_encoding_without_split; try zesu_encoding_split_once).
