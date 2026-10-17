Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.Switches.EncodingNormalization.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Lemma encoding_decided_true (predicate : Prop) `{Decision predicate} (Hbranch : predicate) :
    ite (bool_decide predicate) 1 0 = 1.
Proof.
  zesu_encoding_normalization_if_enabled.
  let statement := type of Hbranch in constr_eq statement predicate.
  reflexivity.
Qed.

Lemma encoding_decided_false (predicate : Prop) `{Decision predicate} (Hbranch : ~ predicate) :
    ite (bool_decide predicate) 1 0 = 0.
Proof.
  zesu_encoding_normalization_if_enabled.
  let statement := type of Hbranch in constr_eq statement constr:(~ predicate).
  reflexivity.
Qed.

Lemma encoding_decision_alias (predicate : Prop) `{Decision predicate} (Hbranch : predicate) :
    ite (bool_decide predicate) 1 0 = 1.
Proof.
  set (decision := bool_decide predicate).
  zesu_encoding_normalization_if_enabled.
  let body := eval unfold decision in decision in
  constr_eq body constr:(bool_decide predicate).
  let statement := type of Hbranch in constr_eq statement predicate.
  reflexivity.
Qed.

Lemma encoding_deciding_equality (predicate : Prop) `{Decision predicate}
    (Hdecision : bool_decide predicate = true) :
    ite (bool_decide predicate) 1 0 = 1.
Proof.
  zesu_encoding_normalization_if_enabled.
  let statement := type of Hdecision in
  constr_eq statement constr:(bool_decide predicate = true).
  reflexivity.
Qed.

Lemma encoding_context_unchanged (left right : bv 64) (size : Z)
    (Hbound : 0 <= size <= 2048)
    (Hcompare : bv_signed (bv_zero_extend 128 left) >= bv_signed (bv_zero_extend 128 right))
    (Hcast : bv_unsigned (Z_to_bv 64 size) > 64) :
    bv_unsigned (Z_to_bv 64 size) = size.
Proof.
  zesu_encoding_normalization_if_enabled.
  let statement := type of Hcompare in
  constr_eq statement constr:(bv_signed (bv_zero_extend 128 left) >= bv_signed (bv_zero_extend 128 right)).
  let statement := type of Hcast in
  constr_eq statement constr:(bv_unsigned (Z_to_bv 64 size) > 64).
  reflexivity.
Qed.

Lemma encoding_hypothesis_only_rejects (left right : bv 64)
    (Hcompare : bv_signed (bv_zero_extend 128 left) >= bv_signed (bv_zero_extend 128 right)) : True.
Proof. assert_fails (idtac; zesu_encoding_normalization_if_enabled). exact I. Qed.

Lemma encoding_outer_fact_does_not_decide (predicate : Prop) `{Decision predicate}
    (value : Z) (Houter : value >= ite (bool_decide predicate) 1 0) : True.
Proof.
  assert_fails (idtac; zesu_encoding_ite_decision constr:(bool_decide predicate)).
  exact I.
Qed.

Lemma encoding_helper_rejects_decided_true (predicate : Prop) `{Decision predicate}
    (Hbranch : predicate) :
    ite (bool_decide predicate) 1 0 = ite (bool_decide predicate) 1 0.
Proof. assert_fails (idtac; zesu_encoding_split_once). reflexivity. Qed.

Lemma encoding_helper_rejects_decided_false (predicate : Prop) `{Decision predicate}
    (Hbranch : ~ predicate) :
    ite (bool_decide predicate) 1 0 = ite (bool_decide predicate) 1 0.
Proof. assert_fails (idtac; zesu_encoding_split_once). reflexivity. Qed.

Lemma encoding_helper_rejects_decision_equality (predicate : Prop) `{Decision predicate}
    (Hdecision : bool_decide predicate = true) :
    ite (bool_decide predicate) 1 0 = ite (bool_decide predicate) 1 0.
Proof. assert_fails (idtac; zesu_encoding_split_once). reflexivity. Qed.

Lemma encoding_immediate_spelling (size : Z) (Hbound : 0 <= size <= 16) :
    ite (bool_decide (bv_unsigned (Z_to_bv 64 size) < bv_signed (@BV 128 9 I))) 1 0 =
    ite (bool_decide (bv_unsigned (Z_to_bv 64 size) < bv_signed (@BV 128 9 I))) 1 0.
Proof.
  zesu_encoding_without_split.
  lazymatch goal with
  | |- ite (bool_decide (bv_unsigned (Z_to_bv 64 size) < bv_signed (@BV 128 9 I))) 1 0 =
       ite (bool_decide (bv_unsigned (Z_to_bv 64 size) < bv_signed (@BV 128 9 I))) 1 0 => idtac
  end.
  reflexivity.
Qed.

Lemma encoding_register_threshold_spelling (value : bv 64) :
    ite (bool_decide (bv_signed (bv_zero_extend 128 value) <
      bv_signed (bv_zero_extend 128 (@BV 64 4096 I)))) 1 0 =
    ite (bool_decide (bv_unsigned value < bv_unsigned (@BV 64 4096 I))) 1 0.
Proof.
  zesu_encoding_without_split.
  lazymatch goal with
  | |- ite (bool_decide (bv_unsigned value < bv_unsigned (@BV 64 4096 I))) 1 0 =
       ite (bool_decide (bv_unsigned value < bv_unsigned (@BV 64 4096 I))) 1 0 => idtac
  end.
  reflexivity.
Qed.

Lemma encoding_threshold_projection_protected (value : bv 64) :
    ite (bool_decide (bv_unsigned value < bv_unsigned (@BV 64 4096 I))) 1 0 =
    ite (bool_decide (bv_unsigned value < bv_unsigned (@BV 64 4096 I))) 1 0.
Proof.
  assert_fails (idtac; zesu_encoding_compute constr:(bv_unsigned (@BV 64 4096 I))).
  reflexivity.
Qed.

Lemma encoding_symbolic_threshold_rejects (value : bv 64) (threshold : Z) : True.
Proof.
  assert_fails (idtac; zesu_encoding_register_threshold
    constr:(bool_decide (bv_signed (bv_zero_extend 128 value) <
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 threshold))))).
  exact I.
Qed.

Lemma encoding_shared_condition (predicate : Prop) `{Decision predicate} :
    ite (bool_decide predicate) 1 0 + 0 = ite (bool_decide predicate) 1 0.
Proof.
  zesu_encoding_normalization_if_enabled.
  all: match goal with _ : ZesuEncodingSplitUsed |- _ => idtac end.
  all: reflexivity.
Qed.

Lemma encoding_no_second_split (first second : Prop) `{Decision first} `{Decision second} :
    ite (bool_decide first) (ite (bool_decide second) 1 0) 0 =
    ite (bool_decide first) (ite (bool_decide second) 1 0) 0.
Proof.
  zesu_encoding_normalization_if_enabled.
  all: assert_fails (idtac; zesu_encoding_split_once).
  all: reflexivity.
Qed.

Lemma encoding_missing_right (predicate : Prop) `{Decision predicate} :
    ite (bool_decide predicate) 1 0 <= 1.
Proof.
  assert_fails (idtac; zesu_encoding_split_once).
  destruct (bool_decide predicate); cbn; lia.
Qed.

Lemma encoding_one_sided_equality (predicate : Prop) `{Decision predicate} :
    ite (bool_decide predicate) 1 0 = 0 \/ ite (bool_decide predicate) 1 0 = 1.
Proof.
  assert_fails (idtac; zesu_encoding_split_once).
  destruct (bool_decide predicate); auto.
Qed.

Lemma encoding_different_conditions (left right : Prop) `{Decision left} `{Decision right}
    (Hsame : left <-> right) :
    ite (bool_decide left) 1 0 = ite (bool_decide right) 1 0.
Proof.
  assert_fails (idtac; zesu_encoding_split_once).
  rewrite (bool_decide_ext left right Hsame). reflexivity.
Qed.

Lemma encoding_no_left_condition (predicate : Prop) `{Decision predicate}
    (Hbranch : predicate) : 1 = ite (bool_decide predicate) 1 0.
Proof.
  assert_fails (idtac; zesu_encoding_split_once).
  zesu_encoding_normalization_if_enabled. reflexivity.
Qed.

Lemma encoding_no_right_condition (predicate : Prop) `{Decision predicate}
    (Hbranch : predicate) : ite (bool_decide predicate) 1 0 = 1.
Proof.
  assert_fails (idtac; zesu_encoding_split_once).
  zesu_encoding_normalization_if_enabled. reflexivity.
Qed.

Lemma encoding_wide_arithmetic_goal (left right : bv 64)
    (Hcompare : bv_unsigned left < bv_unsigned right) :
    bv_signed (bv_zero_extend 128 left) < bv_signed (bv_zero_extend 128 right).
Proof.
  zesu_encoding_normalization_if_enabled.
  let statement := type of Hcompare in constr_eq statement constr:(bv_unsigned left < bv_unsigned right).
  exact Hcompare.
Qed.

Lemma encoding_bounded_arithmetic_goal (size : Z) (Hbound : 0 <= size <= 2048) :
    bv_unsigned (Z_to_bv 64 size) = size.
Proof. zesu_encoding_normalization_if_enabled. reflexivity. Qed.

Lemma encoding_literal_extension_one : bv_zero_extend 64 (Z_to_bv 1 1) = Z_to_bv 64 1.
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_literal_extension_zero : bv_zero_extend 64 (Z_to_bv 1 0) = Z_to_bv 64 0.
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_literal_xor : bv_xor (Z_to_bv 64 7) (Z_to_bv 64 3) = Z_to_bv 64 4.
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_literal_sub : bv_sub (Z_to_bv 64 3) (Z_to_bv 64 5) = Z_to_bv 64 (-2).
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_finish_dispatch (predicate : Prop) `{Decision predicate} (Hbranch : predicate) :
    ite (bool_decide predicate) 1 0 = 1.
Proof. zesu_finish. Qed.

Lemma encoding_symbolic_compute (value : bv 64) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_compute constr:(bv_xor value (Z_to_bv 64 1))).
  assert_fails (idtac; zesu_encoding_compute constr:(bv_sub value (Z_to_bv 64 1))).
  reflexivity.
Qed.

Lemma encoding_symbolic_comparison (value : Z) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_compute constr:(bool_decide (value < 5))).
  reflexivity.
Qed.

Lemma encoding_cached_off (predicate : Prop) `{Decision predicate} (Hbranch : predicate) :
    ite (bool_decide predicate) 1 0 = 1.
Proof.
  assert (Hcache : ZesuSwitchDispatchCache [(ZesuStepEncodingNormalization, false)]) by constructor.
  assert_fails (idtac; zesu_encoding_normalization_if_enabled).
  assert (Hdecision : bool_decide predicate = true) by (apply bool_decide_eq_true_2; exact Hbranch).
  rewrite Hdecision. reflexivity.
Qed.

Lemma encoding_rejected_evar : True.
Proof.
  evar (pending : Z).
  assert_fails (idtac; zesu_encoding_compute constr:(Z_to_bv 64 pending)).
  let value := eval unfold pending in pending in unify value 0%Z.
  exact I.
Qed.

Lemma encoding_symbolic_width (width : N) : True.
Proof. assert_fails (idtac; zesu_encoding_width_literal width). exact I. Qed.

Lemma encoding_nonliteral_operand (value : Z) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_literal_term
    constr:(bv_xor (Z_to_bv 64 value) (Z_to_bv 64 1))).
  reflexivity.
Qed.

Print Assumptions encoding_decided_true.
Print Assumptions encoding_shared_condition.
Print Assumptions encoding_context_unchanged.
Print Assumptions encoding_finish_dispatch.

Require Import ZesuSsz.Compliance.FreeValueBoundRegistrations.

Module ConditionalControls.
Section Controls.
Context {Sigma : gFunctors}.
Definition source (fact : Prop) : iProp Sigma := ⌜fact⌝%I.
Local Typeclasses Opaque source.
#[local] Instance registered fact : ZesuEntryIntro (source fact) fact.
Proof using Sigma. unfold ZesuEntryIntro, source. iIntros "%H". done. Qed.
Definition value (condition : bool) : Z := if condition then 1 else 0.
Ltac mark fact :=
  let marker := fresh "Happlied" in
  pose proof (@ZesuEntryIntroWasApplied Sigma (source fact) fact (registered fact)) as marker.
Lemma keyed_present (P : Prop) (predicate : Prop) `{Decision predicate}
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) (HP : P) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  zesu_encoding_normalization_if_enabled; reflexivity.
Qed.

Lemma keyed_missing_premise (P predicate : Prop) `{Decision predicate}
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)
    (Hresult : value (bool_decide predicate) = 7) : value (bool_decide predicate) = 7.
Proof using Sigma.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  Fail zesu_encoding_conditional_once.
  Fail zesu_encoding_normalization_if_enabled.
  lazymatch goal with |- value (bool_decide predicate) = 7 => idtac end.
  assert_fails (idtac; match goal with _ : ZesuEncodingConditionalUsed _ _ _ _ |- _ => idtac end).
  let statement := type of Hfact in
  constr_eq statement constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  exact Hresult.
Qed.
Lemma keyed_unregistered (P predicate : Prop) `{Decision predicate} (HP : P)
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)
    (Hresult : value (bool_decide predicate) = 7) : value (bool_decide predicate) = 7.
Proof using Sigma. Fail zesu_encoding_conditional_once. Fail zesu_encoding_normalization_if_enabled. exact Hresult. Qed.
Lemma keyed_missing_owned_leaf (P predicate : Prop) `{Decision predicate} (HP : P)
    (Hresult : value (bool_decide predicate) = 7) : value (bool_decide predicate) = 7.
Proof using Sigma.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  Fail zesu_encoding_conditional_once. Fail zesu_encoding_normalization_if_enabled. exact Hresult.
Qed.
Lemma keyed_repeated_call (P predicate : Prop) `{Decision predicate} (HP : P)
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  pose (savedAlias := value (bool_decide predicate)).
  zesu_encoding_conditional_once.
  let original := type of Hfact in
  constr_eq original constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  let body := eval unfold savedAlias in savedAlias in
  constr_eq body constr:(value (bool_decide predicate)).
  change (value (bool_decide predicate) = value (bool_decide predicate)).
  Fail zesu_encoding_conditional_once.
  lazymatch goal with |- value (bool_decide predicate) = value (bool_decide predicate) => idtac end.
  reflexivity.
Qed.
Lemma keyed_duplicate_marker (P predicate : Prop) `{Decision predicate} (HP : P)
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  zesu_encoding_conditional_once. reflexivity.
Qed.
Lemma keyed_ambiguity (P Q predicate : Prop) `{Decision predicate} (HP : P)
    (Hfacts : (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) /\
              (Q -> value (bool_decide predicate) = if bool_decide predicate then 2 else 0)) :
    value (bool_decide predicate) = value (bool_decide predicate).
Proof using Sigma.
  mark constr:((P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) /\
               (Q -> value (bool_decide predicate) = if bool_decide predicate then 2 else 0)).
  Fail try zesu_encoding_normalization_if_enabled.
  Fail first [zesu_encoding_normalization_if_enabled | idtac].
  reflexivity.
Qed.
Lemma keyed_ambiguity_reversed (P Q predicate : Prop) `{Decision predicate} (HP : P)
    (Hfacts : (Q -> value (bool_decide predicate) = if bool_decide predicate then 2 else 0) /\
              (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)) :
    value (bool_decide predicate) = value (bool_decide predicate).
Proof using Sigma.
  mark constr:((Q -> value (bool_decide predicate) = if bool_decide predicate then 2 else 0) /\
               (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)).
  Fail try zesu_encoding_normalization_if_enabled. reflexivity.
Qed.
Lemma keyed_owned_conjunction (P predicate : Prop) `{Decision predicate} (HP : P)
    (Hfacts : True /\ (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma.
  mark constr:(True /\ (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0)).
  zesu_encoding_conditional_once. reflexivity.
Qed.
Section RegisteredPremise.
Context (P : Prop) (HP : SimplAnd P True).
#[local] Existing Instance HP.
#[local] Instance pure_fact_switch : ZesuStepPureFactHints := I.
Lemma keyed_registered_premise (predicate : Prop) `{Decision predicate}
    (Hfact : P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma HP.
  mark constr:(P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  zesu_encoding_conditional_once. reflexivity.
Qed.
End RegisteredPremise.
Section ExistingBound.
#[local] Instance existing_bound_switch : ZesuStepPureFactHints := I.
Lemma keyed_existing_bound (size : Z) (predicate : Prop) `{Decision predicate}
    (Hfact : (0 <= freeSizeClassOfBytes size <= 22) ->
      value (bool_decide predicate) = if bool_decide predicate then 1 else 0) :
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0.
Proof using Sigma.
  mark constr:((0 <= freeSizeClassOfBytes size <= 22) ->
    value (bool_decide predicate) = if bool_decide predicate then 1 else 0).
  zesu_encoding_conditional_once. reflexivity.
Qed.
End ExistingBound.
End Controls.
End ConditionalControls.

Require Import ZesuSsz.Automation.Switches.EntryIntro.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
Require Import ZesuSsz.Compliance.FreeDataRegistrations.
Require Import ZesuSsz.Compliance.FreeUnfoldRegistrations.
Require Import ZesuSsz.Compliance.FreeSizeClassIteFacts.
Section ExactSpec.
Context `{!islaG Sigma} `{!threadG}.
Lemma keyed_spec_immediate args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte)
    (Hrange : 0 <= freeBufferLength args <= 16) :
  freeEntryAt80041f7c args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜freeSizeClassOfBytes (freeBufferLength args) =
    bv_unsigned (bv_xor (bv_zero_extend 64
      (ite (bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args)))
        (@bv_signed 128 (@BV 128 9 I)))) (Z_to_bv 1 1) (Z_to_bv 1 0)))
      (Z_to_bv 64 1))⌝.
Proof.
  iIntros "Hsource". zesu_entry_intro_if_enabled. iPureIntro.
  zesu_encoding_normalization_if_enabled; reflexivity.
Qed.
End ExactSpec.
