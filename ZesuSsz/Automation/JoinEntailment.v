Require Import lithium.interpreter.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.AdditiveDecoder.
Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.ByteClassGuards.
Require Import ZesuSsz.Automation.ListHeadFromLength.
Require Import ZesuSsz.Automation.SourceFaultProof.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith Lia Bool.Bool Strings.String.
From iris.proofmode Require Import tactics environments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma zesu_join_cancel_right width (left right : bv width) :
  bv_sub (bv_add left right) right = left.
Proof.
  apply bv_eq.
  rewrite bv_sub_unsigned.
  rewrite bv_add_unsigned.
  rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned left + bv_unsigned right - bv_unsigned right)
    with (bv_unsigned left) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma zesu_join_cancel_shared width (left right common : bv width) :
  bv_sub (bv_add (bv_add left common) right) (bv_add right common) = left.
Proof.
  apply bv_eq.
  repeat rewrite bv_sub_unsigned.
  repeat rewrite bv_add_unsigned.
  rewrite bv_wrap_sub_idemp_l.
  rewrite bv_wrap_sub_idemp_r.
  replace (bv_wrap width (bv_unsigned left + bv_unsigned common) + bv_unsigned right -
    (bv_unsigned right + bv_unsigned common))
    with (bv_wrap width (bv_unsigned left + bv_unsigned common) - bv_unsigned common) by lia.
  rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned left + bv_unsigned common - bv_unsigned common)
    with (bv_unsigned left) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Ltac zesu_join_open_source :=
  iIntros "[HjoinSource HjoinContinuation]";
  iRevert "HjoinSource";
  repeat liForall;
  iIntros "HjoinSource";
  ResourceGroups.zesu_open_resource_groups.

Ltac zesu_join_pack_target unfold_target :=
  unfold_target;
  cbn zeta;
  iFrame "HjoinContinuation";
  repeat iExists _;
  iFrame;
  repeat rewrite zesu_join_cancel_right;
  repeat rewrite zesu_join_cancel_shared;
  iFrame.

Ltac zesu_join_resource_entry unfold_target :=
  zesu_join_open_source;
  zesu_join_pack_target unfold_target.

(* Expose only transparent conjunction views; retain the original hypothesis. *)
Ltac zesu_join_conjunction_view fuel proposition :=
  lazymatch fuel with
  | O => fail
  | S _ =>
      let view := eval hnf in proposition in
      lazymatch view with
      | ?left /\ ?right => constr:(left /\ right)
      end
  end.

Ltac zesu_join_fact_absent proposition :=
  assert_fails ltac:(idtac; multimatch goal with Hknown : ?known |- _ =>
    constr_eq known proposition
  end).

Ltac zesu_join_add_fact proof :=
  let proposition := type of proof in
  zesu_join_fact_absent proposition;
  let Hview := fresh "HjoinView" in pose proof proof as Hview.

Ltac zesu_join_project_once :=
  multimatch goal with Hsource : ?proposition |- _ =>
    let sort := type of proposition in constr_eq sort constr:(Prop);
    let view := zesu_join_conjunction_view constr:(16%nat) proposition in
    lazymatch view with ?left /\ ?right =>
      first [zesu_join_add_fact constr:(@proj1 left right Hsource) |
             zesu_join_add_fact constr:(@proj2 left right Hsource)]
    end
  end.

Ltac zesu_join_boolean_once :=
  multimatch goal with
  | Hsource : bool_decide ?proposition = true |- _ =>
    zesu_join_fact_absent proposition;
    let Hview := fresh "HjoinBoolean" in pose proof Hsource as Hview;
    apply bool_decide_eq_true_1 in Hview
  | Hsource : negb (bool_decide ?proposition) = true |- _ =>
    let negative := constr:(~ proposition) in
    zesu_join_fact_absent negative;
    let Hview := fresh "HjoinBoolean" in pose proof Hsource as Hview;
    apply Bool.negb_true_iff in Hview;
    apply bool_decide_eq_false_1 in Hview
  end.

Lemma zesu_join_word_codec count width (word : bv width) :
  0 <= count -> count * 8 = Z.of_N width ->
  zesu_additive_decoder 8 (bv_to_little_endian count 8 (bv_unsigned word)) = bv_unsigned word.
Proof.
  intros Hcount Hwidth.
  rewrite (zesu_additive_decoder_view 8 (bv_to_little_endian count 8 (bv_unsigned word))).
  rewrite (little_endian_to_bv_to_little_endian count 8 (bv_unsigned word) Hcount).
  change (bv_unsigned word mod 2 ^ (count * 8) = bv_unsigned word).
  rewrite Hwidth. apply Z.mod_small. exact (bv_unsigned_in_range width word).
Qed.

Lemma zesu_join_literal_guard (word : bv 8) :
  negb (bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 word)) < bv_signed (BV 128 0))) = true ->
  bv_unsigned word <= 127.
Proof.
  intros Hguard. apply Bool.negb_true_iff in Hguard.
  apply bool_decide_eq_false_1 in Hguard.
  rewrite (bv_sign_extend_signed 128 (bv_sign_extend 64 word) ltac:(lia)) in Hguard.
  rewrite (bv_sign_extend_signed 64 word ltac:(lia)) in Hguard.
  rewrite bv_signed_BV in Hguard. rewrite bv_swrap_0 in Hguard.
  pose proof (bv_signed_in_range 8 word ltac:(discriminate)) as Hrange.
  assert (Hrepr : Z_to_bv 8 (bv_signed word) = word).
  { apply bv_eq_signed. rewrite Z_to_bv_signed. apply bv_swrap_bv_signed. }
  assert (Hsmall : 0 <= bv_signed word < bv_modulus 8).
  { change (0 <= bv_signed word < 256). change (-128 <= bv_signed word < 128) in Hrange. lia. }
  rewrite <- Hrepr at 1. rewrite (Z_to_bv_small 8 (bv_signed word) Hsmall).
  change (-128 <= bv_signed word < 128) in Hrange. lia.
Qed.

Lemma zesu_join_mask_payload (word : bv 8) :
  128 <= bv_unsigned word ->
  bv_unsigned (bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255)) (BV 64 127)) = bv_unsigned word - 128.
Proof.
  intros Hhigh. pose proof (bv_unsigned_in_range 8 word) as Hrange.
  change (0 <= bv_unsigned word < 256) in Hrange.
  pose proof (zesu_sign_extended_byte_mask 64 word ltac:(lia)) as Hmask.
  assert (Hliteral : Z_to_bv 64 (2 ^ 8 - 1) = BV 64 255).
  { apply bv_eq. vm_compute. reflexivity. }
  rewrite Hliteral in Hmask. rewrite Hmask. rewrite bv_and_unsigned.
  rewrite (Z_to_bv_small 64 (bv_unsigned word) ltac:(change (0 <= bv_unsigned word < 18446744073709551616); lia)).
  rewrite bv_unsigned_BV.
  change (Z.land (bv_unsigned word) (Z.ones 7) = bv_unsigned word - 128).
  rewrite (Z.land_ones (bv_unsigned word) 7 ltac:(lia)).
  change (bv_unsigned word mod 128 = bv_unsigned word - 128).
  replace (bv_unsigned word) with (bv_unsigned word - 128 + 1 * 128) at 1 by lia.
  rewrite (Z.mod_add (bv_unsigned word - 128) 1 128 ltac:(lia)).
  apply Z.mod_small. lia.
Qed.

Lemma zesu_join_nonzero_cast width quantity (zero : bv width) :
  bv_unsigned zero = 0 -> Z_to_bv width quantity <> zero -> quantity <> 0.
Proof.
  intros Hzero Hnonzero Hquantity. subst quantity.
  apply Hnonzero. apply bv_eq.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_0. symmetry. exact Hzero.
Qed.

Ltac zesu_join_nonzero_once :=
  multimatch goal with
  | Hnonzero : Z_to_bv ?width ?quantity <> ?zero |- _ =>
    is_closed_term width; is_closed_term zero;
    let Hzero := constr:(ltac:(vm_compute; reflexivity) : bv_unsigned zero = 0) in
    zesu_join_add_fact constr:(zesu_join_nonzero_cast width quantity zero Hzero Hnonzero)
  end.

Ltac zesu_join_positive_once :=
  multimatch goal with Hnonzero : ?quantity <> 0 |- _ =>
    let positive := constr:(0 < quantity) in
    zesu_join_fact_absent positive;
    let Hpositive := fresh "HjoinPositive" in assert (Hpositive : positive) by lia
  end.

Ltac zesu_join_cast_once :=
  multimatch goal with Hsource : ?proposition |- _ =>
    lazymatch proposition with context [Z_to_bv 64 ?quantity] =>
      let equality := constr:(bv_unsigned (Z_to_bv 64 quantity) = quantity) in
      zesu_join_fact_absent equality;
      let Hcast := fresh "HjoinCast" in
      assert (Hcast : equality) by Hooks.zesu_stack_arithmetic
    end
  end.

Ltac zesu_join_literal_once :=
  multimatch goal with
  | Hguard : negb (bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?word)) < bv_signed (BV 128 0))) = true |- _ =>
    zesu_join_add_fact constr:(zesu_join_literal_guard word Hguard)
  end.

Ltac zesu_join_prepare_pure :=
  repeat zesu_join_project_once;
  repeat zesu_join_boolean_once;
  repeat zesu_join_nonzero_once;
  repeat zesu_join_positive_once;
  repeat zesu_join_literal_once;
  try ByteClassGuards.zesu_byte_class_guards;
  repeat zesu_join_project_once;
  repeat zesu_join_cast_once.

Ltac zesu_join_head_goal :=
  lazymatch goal with
  | |- ?bytes = ?head :: ?tail =>
    unify head (List.nth 0 bytes (BV 8 0));
    unify tail (List.skipn 1 bytes);
    ListHeadFromLength.zesu_list_head_from_length
  end.

(* Select the source bounds before arithmetic; their width presentations may
   be definitionally equal without matching syntactically. *)
Ltac zesu_join_class_side :=
  lazymatch goal with |- ?lower <= ?value <= ?upper =>
    multimatch goal with Hne : ?different <> ?base |- _ =>
      unify value different;
      multimatch goal with Hlo : ?baseLo <= ?valueLo |- _ =>
        unify baseLo base; unify valueLo value;
        multimatch goal with Hhi : ?valueHi <= ?upperHi |- _ =>
          unify valueHi value; unify upperHi upper;
          change (lower <= valueLo <= upper);
          clear - Hlo Hhi Hne; lia
        end
      end
    end
  end.

Ltac zesu_join_semantic_side views :=
  first [solve [eassumption] | solve [reflexivity] |
    solve [zesu_join_class_side] |
    solve [split; zesu_join_semantic_side views] |
    solve [progress views; zesu_join_semantic_side views] |
    solve [zesu_join_head_goal] | solve [lia] |
    solve [Hooks.zesu_stack_arithmetic]].

Ltac zesu_join_contradiction :=
  multimatch goal with
  | Hleaf : negb (bool_decide
      (bv_signed (bv_add (bv_zero_extend 128 ?pointer) ?extent) <=
       bv_signed (bv_zero_extend 128 ?endpoint))) = true |- _ =>
    exfalso; SourceFaultProof.zesu_source_fault_proof ltac:(idtac) Hleaf
  end.

(* Detect the supported fault guard before projecting unrelated pure views. *)
Ltac zesu_join_fault_refute :=
  multimatch goal with
  | Hleaf : negb (bool_decide
      (bv_signed (bv_add (bv_zero_extend 128 ?pointer) ?extent) <=
       bv_signed (bv_zero_extend 128 ?endpoint))) = true |- _ => idtac
  end;
  repeat zesu_join_boolean_once;
  repeat zesu_join_nonzero_once;
  zesu_join_contradiction.

Ltac zesu_join_image :=
  first [solve [multimatch goal with
    | Hlength : List.length ?bytes = ?count |- ?target =>
        lazymatch target with context [bytes] =>
          clear - Hlength; ByteClassGuards.zesu_byte_class_image
        end
    end] | ByteClassGuards.zesu_byte_class_image].

Ltac zesu_join_meaning_goal semantic views :=
  lazymatch goal with |- ?predicate ?actual =>
    lazymatch type of actual with list (bv 8) =>
      let canonical := open_constr:(_ : list (bv 8)) in
      let Hmeaning := fresh "HjoinMeaning" in
      assert (Hmeaning : predicate canonical) by
        (semantic; zesu_join_semantic_side views);
      assert_fails (has_evar canonical);
      let Himage := fresh "HjoinImage" in
      assert (Himage : actual = canonical) by
        (try views; zesu_join_image);
      rewrite Himage; exact Hmeaning
    end
  end.

Ltac zesu_join_finish_coq semantic views :=
  first [solve [assumption] |
    lazymatch goal with |- ?proposition =>
      let head := get_head proposition in constr_eq head constr:(and);
      split; zesu_join_finish_coq semantic views
    end |
    solve [zesu_join_contradiction] |
    zesu_join_meaning_goal semantic views].

Ltac zesu_join_finish_resource semantic views :=
  lazymatch goal with
  | |- envs_entails _ (bi_pure _) =>
      iPureIntro; zesu_join_finish_coq semantic views
  | |- envs_entails _ (bi_sep _ _) =>
      iSplit; zesu_join_finish_resource semantic views
  end.

(* Callbacks expose owned definitions and apply an owned semantic lemma. *)
Ltac zesu_join_finish_open_source refute unfold_target semantic views :=
  first [solve [exfalso; refute] |
    zesu_join_pack_target unfold_target;
    zesu_join_prepare_pure;
    zesu_join_finish_resource semantic views].

Ltac zesu_join_entailment_with_refutation refute unfold_target semantic views :=
  solve [zesu_join_open_source;
    zesu_join_finish_open_source refute unfold_target semantic views].

Ltac zesu_join_entailment unfold_target semantic views :=
  zesu_join_entailment_with_refutation ltac:(zesu_join_fault_refute)
    unfold_target semantic views.
