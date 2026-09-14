Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Lemma zesu_packed_u64_lookup count index (bytes : list (bv 8)) :
  length bytes = (count * 8)%nat -> (index < count)%nat ->
  u64s_of_bytes count bytes !! index = Some
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index * 8) bytes)))).
Proof.
  intros Hlength Hindex. unfold u64s_of_bytes.
  rewrite list_lookup_fmap. rewrite sublist_lookup_reshape; try lia.
  unfold sublist_lookup. case_decide; [reflexivity|lia].
Qed.
Lemma zesu_packed_window_take_drop {A} (bytes : list A) start width index size :
  (index + width <= size)%nat ->
  take width (drop index (take size (drop start bytes))) =
    take width (drop (start + index) bytes).
Proof.
  intros Hbound. rewrite take_drop_commute take_take Nat.min_l; try lia.
  rewrite <- take_drop_commute. rewrite drop_drop. reflexivity.
Qed.
Lemma zesu_packed_u64_window count index start (bytes : list (bv 8)) :
  (start + count * 8 <= length bytes)%nat -> (index < count)%nat ->
  default (BV 64 0)
    (u64s_of_bytes count (take (count * 8) (drop start bytes)) !! index) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (start + index * 8) bytes))).
Proof.
  intros Hbound Hindex.
  rewrite zesu_packed_u64_lookup; [|rewrite length_take length_drop; lia|assumption].
  simpl. rewrite zesu_packed_window_take_drop; [reflexivity|lia].
Qed.
Print Assumptions zesu_packed_u64_lookup.
Print Assumptions zesu_packed_window_take_drop.
Print Assumptions zesu_packed_u64_window.


Ltac zesu_packed_word_window_shape value :=
  let expanded := lazymatch value with
    | default _ (_ !! _) => value
    | _ => let head := get_head value in eval cbv beta delta [head] in value
    end in
  lazymatch expanded with default (BV 64 0) (?packed !! ?index) =>
    let words := lazymatch packed with
      | u64s_of_bytes _ _ => packed
      | _ => let head := get_head packed in eval cbv beta delta [head] in packed
      end in
    lazymatch words with u64s_of_bytes ?count (take ?size (drop ?start ?bytes)) =>
      constr:((count, index, start, bytes))
    end
  end.
Ltac zesu_normalize_packed_word_value value :=
  let shape := zesu_packed_word_window_shape value in
  lazymatch shape with (?count, ?index, ?start, ?bytes) =>
    let canonical := constr:(Z_to_bv 64
      (little_endian_to_bv 8 (take 8 (drop (start + index * 8)%nat bytes)))) in
    let Heq := fresh "HpackedWordValue" in
    assert (Heq : value = canonical) by
      (change (default (BV 64 0)
        (u64s_of_bytes count (take (count * 8) (drop start bytes)) !! index) = canonical);
       apply zesu_packed_u64_window; lia);
    progress rewrite Heq; clear Heq
  end.
Ltac zesu_normalize_packed_word_subsume :=
  lazymatch goal with
  | |- envs_entails _ (subsume _ ?requested _) =>
      let target := eval cbv beta zeta in (requested tt) in
      lazymatch target with (?address ↦ₘ{?q} ?value)%I =>
        zesu_normalize_packed_word_value value
      end
  end.
