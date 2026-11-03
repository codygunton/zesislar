(* Automation library: Hooks requires this file without importing its opt-in instance. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Bool.Bool.
From stdpp Require Import list decidable tactics.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.VmClosed.

Import ListNotations.
Local Open Scope Z_scope.
Set Default Proof Mode "Classic".

(* Inputs are existing proof terms, not a second canonical fact schema. *)
Module CanonicalFactAdapter.

Lemma decision_view (P : Prop) `{!Decision P} :
  P -> bool_decide P = true.
Proof. apply bool_decide_eq_true_2. Qed.

Lemma closed_interval_boolean (lower value upper : Z) :
  lower <= value -> value <= upper ->
  (bool_decide (lower <= value) && bool_decide (value <= upper)) = true.
Proof.
  intros Hlower Hupper. apply andb_true_iff. split;
    apply bool_decide_eq_true_2; assumption.
Qed.

Lemma word_link (width : N) (word : bv width) (value : Z) :
  bv_unsigned word = value -> word = Z_to_bv width value.
Proof. intros Hvalue. rewrite <- Hvalue. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma word_equality (width : N) (left right : bv width) :
  bv_unsigned left = bv_unsigned right -> left = right.
Proof. apply (proj2 (zesu_guard_bv_eq_iff width left right)). Qed.

Lemma signed_extended_le (left right : bv 64) :
  bv_unsigned left <= bv_unsigned right ->
  bv_signed (bv_zero_extend 128 left) <= bv_signed (bv_zero_extend 128 right).
Proof. rewrite !zesu_signed_zero_extend_64_128. exact (fun H => H). Qed.

Lemma signed_extended_lt (left right : bv 64) :
  bv_unsigned left < bv_unsigned right ->
  bv_signed (bv_zero_extend 128 left) < bv_signed (bv_zero_extend 128 right).
Proof. apply zesu_unsigned_lt_signed_zero_extend_64_128. Qed.

Lemma nat_le_Z (left right : nat) :
  (left <= right)%nat -> Z.of_nat left <= Z.of_nat right.
Proof. apply (proj1 (Nat2Z.inj_le left right)). Qed.

Lemma nat_lt_Z (left right : nat) :
  (left < right)%nat -> Z.of_nat left < Z.of_nat right.
Proof. apply (proj1 (Nat2Z.inj_lt left right)). Qed.

Lemma N_le_Z (left right : N) :
  (left <= right)%N -> Z.of_N left <= Z.of_N right.
Proof. apply (proj1 (N2Z.inj_le left right)). Qed.

Lemma N_lt_Z (left right : N) :
  (left < right)%N -> Z.of_N left < Z.of_N right.
Proof. apply (proj1 (N2Z.inj_lt left right)). Qed.

Lemma address_sum (base : bv 64) (offset : Z) :
  0 <= bv_unsigned base + offset < 2 ^ 64 ->
  bv_unsigned (base + Z_to_bv 64 offset)%bv = bv_unsigned base + offset.
Proof.
  intros Hsum. rewrite bv_add_unsigned Z_to_bv_unsigned bv_wrap_add_idemp_r.
  apply bv_wrap_small. exact Hsum.
Qed.

Lemma ge_le (left right : Z) : left >= right -> right <= left.
Proof. apply Z.ge_le. Qed.

Lemma gt_lt (left right : Z) : left > right -> right < left.
Proof. apply Z.gt_lt. Qed.

Lemma address_difference (base : bv 64) (offset : Z) :
  0 <= offset -> bv_unsigned base + offset < 2 ^ 64 ->
  bv_unsigned (base + Z_to_bv 64 offset)%bv - bv_unsigned base = offset.
Proof. apply zesu_bv_unsigned_add_Z_64. Qed.

Lemma access_end (address region_end width : Z) :
  address <= region_end - width -> address + width <= region_end.
Proof. intros Hbound. lia. Qed.

(* Modulo is not an implemented input form. This view needs a proven multiple. *)
Lemma congruence_from_multiple (address multiple modulus : Z) :
  0 < modulus -> address = multiple * modulus -> address mod modulus = 0.
Proof.
  intros Hmodulus Hmultiple. rewrite Hmultiple.
  apply Z.mod_mul. lia.
Qed.

Lemma list_length_view {A : Type} (left right : list A) :
  left = right -> length left = length right.
Proof. apply (f_equal (@length A)). Qed.

(* These lookup outputs follow from supported list equalities and bounds. *)
Lemma list_head_view {A : Type} (values tail : list A) (value : A) :
  values = [value] ++ tail -> values !! 0%nat = Some value.
Proof. intros Hvalues. rewrite Hvalues. reflexivity. Qed.

Lemma list_prefix_view {A : Type} (values prefix suffix : list A) (index : nat) :
  values = prefix ++ suffix -> (index < length prefix)%nat ->
  values !! index = prefix !! index.
Proof. intros Hvalues Hbound. rewrite Hvalues. apply lookup_app_l. exact Hbound. Qed.

Lemma bounded_splice_length {A : Type} (values replacement : list A) (index : nat) :
  (index + length replacement <= length values)%nat ->
  length (take index values ++ replacement ++
    drop (index + length replacement) values) = length values.
Proof.
  intros Hbound.
  change (length (sublist_alter (fun _ : list A => replacement)
    index (length replacement) values) = length values).
  eapply length_sublist_alter.
  - apply sublist_lookup_Some. exact Hbound.
  - reflexivity.
Qed.

(* Forall inputs are not implemented. This property follows from the element type. *)
Lemma intrinsic_byte_ranges (values : list (bv 8)) :
  Forall (fun value => 0 <= bv_unsigned value < bv_modulus 8) values.
Proof.
  apply Forall_forall. intros value Hmember. apply bv_unsigned_in_range.
Qed.

End CanonicalFactAdapter.

Ltac zesu_canonical_term_fixed term :=
  assert_fails ltac:(idtac; has_evar term).

(* Check every local body once, including aliases unrelated to the supplied fact. *)
Ltac zesu_canonical_local_definitions_fixed :=
  assert_fails ltac:(idtac;
    multimatch goal with
    | local := ?body : _ |- _ => has_evar body
    end).

(* Hot calls use this after the enclosing adapter entry checks local bodies. *)
Ltac zesu_canonical_input_term_fixed proof :=
  zesu_canonical_term_fixed proof;
  let statement := type of proof in
  zesu_canonical_term_fixed statement.

(* Preserve the checked direct entry used by the refusal controls. *)
Ltac zesu_canonical_input_fixed proof :=
  zesu_canonical_local_definitions_fixed;
  zesu_canonical_input_term_fixed proof.

Ltac zesu_canonical_learn proof := try learn_hyp proof.

(* Inspect supplied proof terms only. Do not inspect or change the current target. *)
Ltac zesu_canonical_leaf_views proof :=
  zesu_canonical_input_term_fixed proof;
  let statement := type of proof in
  zesu_canonical_learn proof;
  lazymatch statement with
  | True => idtac
  | Z.le _ _ =>
      zesu_canonical_learn (CanonicalFactAdapter.decision_view _ proof);
      try lazymatch statement with
      | bv_unsigned ?left <= bv_unsigned ?right =>
          lazymatch type of left with bv 64 => idtac end;
          lazymatch type of right with bv 64 => idtac end;
          zesu_canonical_learn (CanonicalFactAdapter.signed_extended_le left right proof)
      end
  | Z.ge ?left ?right =>
      zesu_canonical_leaf_views (CanonicalFactAdapter.ge_le left right proof)
  | Z.gt ?left ?right =>
      zesu_canonical_leaf_views (CanonicalFactAdapter.gt_lt left right proof)
  | Z.lt _ _ =>
      zesu_canonical_learn (CanonicalFactAdapter.decision_view _ proof);
      try lazymatch statement with
      | bv_unsigned ?left < bv_unsigned ?right =>
          lazymatch type of left with bv 64 => idtac end;
          lazymatch type of right with bv 64 => idtac end;
          zesu_canonical_learn (CanonicalFactAdapter.signed_extended_lt left right proof)
      end
  | @eq Z _ _ =>
      zesu_canonical_learn (CanonicalFactAdapter.decision_view _ proof);
      try lazymatch statement with
      | bv_unsigned ?word = ?value =>
          lazymatch type of word with bv ?width =>
            zesu_canonical_learn (CanonicalFactAdapter.word_link width word value proof)
          end
      end;
      try lazymatch statement with
      | bv_unsigned ?left = bv_unsigned ?right =>
          lazymatch type of left with bv ?width =>
            zesu_canonical_learn (CanonicalFactAdapter.word_equality width left right proof)
          end
      end
  | Nat.le ?left ?right => zesu_canonical_learn (CanonicalFactAdapter.nat_le_Z left right proof)
  | Nat.lt ?left ?right => zesu_canonical_learn (CanonicalFactAdapter.nat_lt_Z left right proof)
  | N.le ?left ?right => zesu_canonical_learn (CanonicalFactAdapter.N_le_Z left right proof)
  | N.lt ?left ?right => zesu_canonical_learn (CanonicalFactAdapter.N_lt_Z left right proof)
  | @eq nat _ _ => zesu_canonical_learn (f_equal Z.of_nat proof)
  | @eq N _ _ => zesu_canonical_learn (f_equal Z.of_N proof)
  | @eq (list ?A) ?left ?rhs =>
      zesu_canonical_learn (CanonicalFactAdapter.list_length_view left rhs proof);
      try lazymatch type of left with
      | list (bv 8) =>
          zesu_canonical_learn (CanonicalFactAdapter.intrinsic_byte_ranges left)
      end;
      try lazymatch rhs with
      | [?value] ++ ?tail =>
          zesu_canonical_learn (CanonicalFactAdapter.list_head_view left tail value proof)
      end
  | _ => fail 0 "The supplied proof has no supported canonical fact view"
  end.

Ltac zesu_canonical_pair_views first_proof second_proof :=
  let first_statement := type of first_proof in
  let second_statement := type of second_proof in
  try (lazymatch first_statement with
    | ?lower <= ?value =>
        lazymatch second_statement with
        | value < ?upper => zesu_canonical_learn (conj first_proof second_proof)
        | value <= ?upper =>
            zesu_canonical_learn (conj first_proof second_proof);
            zesu_canonical_learn (CanonicalFactAdapter.closed_interval_boolean
              lower value upper first_proof second_proof)
        end
    end);
  try (lazymatch first_statement with
    | 0 <= ?offset =>
        lazymatch second_statement with
        | bv_unsigned ?base + offset < 2 ^ 64 =>
            zesu_canonical_learn (CanonicalFactAdapter.address_difference
              base offset first_proof second_proof)
        end
    end);
  try (lazymatch first_statement with
    | 0 <= bv_unsigned ?base + ?offset =>
        lazymatch second_statement with
        | bv_unsigned base + offset < 2 ^ 64 =>
            zesu_canonical_learn (CanonicalFactAdapter.address_sum
              base offset (conj first_proof second_proof))
        end
    end);
  try (lazymatch first_statement with
    | 0 < ?modulus =>
        lazymatch second_statement with
        | ?address = ?multiple * modulus =>
            zesu_canonical_learn (CanonicalFactAdapter.congruence_from_multiple
              address multiple modulus first_proof second_proof)
        end
    end);
  try (lazymatch first_statement with
    | @eq (list ?A) ?values (?prefix ++ ?suffix) =>
        lazymatch second_statement with
        | (?index < length prefix)%nat =>
            zesu_canonical_learn (CanonicalFactAdapter.list_prefix_view
              values prefix suffix index first_proof second_proof)
        end
    end).

Ltac zesu_canonical_leaves facts continuation :=
  let statement := type of facts in
  lazymatch statement with
  | _ /\ _ =>
      zesu_canonical_leaves (proj1 facts) continuation;
      zesu_canonical_leaves (proj2 facts) continuation
  | _ => continuation facts
  end.

(* One shared entry point. Keep the supplied facts and all owned resources intact. *)
Ltac zesu_canonical_fact_views_core facts :=
  zesu_canonical_input_term_fixed facts;
  zesu_canonical_leaves facts ltac:(fun first_proof =>
    zesu_canonical_leaf_views first_proof;
    zesu_canonical_leaves facts ltac:(fun second_proof =>
      zesu_canonical_pair_views first_proof second_proof)).

Ltac zesu_canonical_fact_views facts :=
  zesu_canonical_local_definitions_fixed;
  zesu_canonical_fact_views_core facts.

(* Context integration never unfolds metadata or consumes an Iris resource. *)
(* Pair keys share the term required by the unchanged combining lemma. *)
Ltac zesu_canonical_context_step_core :=
  first [
    match goal with
    | proof : _ |- _ => progress (zesu_canonical_fact_views_core proof)
    end
  | match goal with
    | lo : ?lower <= ?value, hi : ?value < ?upper |- _ =>
        zesu_canonical_input_term_fixed lo; zesu_canonical_input_term_fixed hi;
        progress (zesu_canonical_pair_views lo hi)
    | lo : ?lower <= ?value, hi : ?value <= ?upper |- _ =>
        zesu_canonical_input_term_fixed lo; zesu_canonical_input_term_fixed hi;
        progress (zesu_canonical_pair_views lo hi)
    | lo : 0 <= ?offset, hi : bv_unsigned ?base + ?offset < 2 ^ 64 |- _ =>
        zesu_canonical_input_term_fixed lo; zesu_canonical_input_term_fixed hi;
        progress (zesu_canonical_pair_views lo hi)
    | lo : 0 <= bv_unsigned ?base + ?offset,
      hi : bv_unsigned ?base + ?offset < 2 ^ 64 |- _ =>
        zesu_canonical_input_term_fixed lo; zesu_canonical_input_term_fixed hi;
        progress (zesu_canonical_pair_views lo hi)
    | positive : 0 < ?modulus, multiple : ?address = ?factor * ?modulus |- _ =>
        zesu_canonical_input_term_fixed positive; zesu_canonical_input_term_fixed multiple;
        progress (zesu_canonical_pair_views positive multiple)
    | parts : @eq (list ?A) ?values (?prefix ++ ?suffix),
      inside : (?index < length ?prefix)%nat |- _ =>
        zesu_canonical_input_term_fixed parts; zesu_canonical_input_term_fixed inside;
        progress (zesu_canonical_pair_views parts inside)
    end ].

(* Keep the public no-action failure behavior used by existing controls. *)
Ltac zesu_canonical_context_step :=
  zesu_canonical_local_definitions_fixed;
  zesu_canonical_context_step_core.

Class ZesuStepCanonicalFactAdapter : Prop :=
  zesu_step_canonical_fact_adapter : True.

(* Require alone does not import this opt-in instance. *)
#[export] Instance zesu_canonical_fact_adapter_enabled :
  ZesuStepCanonicalFactAdapter := I.
