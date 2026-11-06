Require Import ZesuSsz.Automation.SwitchDispatch.
From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions list_numbers.
Import ListNotations.
Local Open Scope Z_scope.

Class ZesuStepFramePacking : Prop := {}.

Lemma zesu_pack_decoded_slices (width : N) (left_count right_count : nat)
    (bytes : list (bv width)) (left_value right_value : Z) :
  length bytes = (left_count + right_count)%nat ->
  little_endian_to_bv width (firstn left_count bytes) = left_value ->
  little_endian_to_bv width
    (firstn right_count (skipn left_count bytes)) = right_value ->
  bytes = bv_to_little_endian (Z.of_nat left_count) width left_value ++
    bv_to_little_endian (Z.of_nat right_count) width right_value.
Proof.
  intros Hlength Hleft Hright.
  assert (Hleft_length : length (firstn left_count bytes) = left_count).
  { rewrite firstn_length. lia. }
  assert (Htail_length : length (skipn left_count bytes) = right_count).
  { rewrite skipn_length. lia. }
  assert (Hright_full : firstn right_count (skipn left_count bytes) =
      skipn left_count bytes).
  { apply firstn_all2. lia. }
  rewrite <- Hleft, <- Hright.
  rewrite (bv_to_little_endian_to_bv (Z.of_nat left_count) width
    (firstn left_count bytes)); [|rewrite Hleft_length; reflexivity].
  rewrite (bv_to_little_endian_to_bv (Z.of_nat right_count) width
    (firstn right_count (skipn left_count bytes))).
  - rewrite Hright_full. symmetry. apply firstn_skipn.
  - rewrite Hright_full, Htail_length. reflexivity.
Qed.

(* The caller supplies its existing decoder equality normalization. *)
Ltac zesu_frame_packing normalize_decoder :=
  zesu_switch_enabled constr:(ZesuStepFramePacking);
  lazymatch goal with
  | |- @eq (list (bv _)) _
      (bv_to_little_endian _ _ _ ++ bv_to_little_endian _ _ _) => idtac
  end;
  normalize_decoder;
  repeat match goal with
  | Hslice : context [skipn 0 ?values] |- _ => rewrite skipn_O in Hslice
  end;
  rewrite ?skipn_O;
  lazymatch goal with
  | |- ?bytes = bv_to_little_endian ?left_count ?width ?left_value ++
      bv_to_little_endian ?right_count ?width ?right_value =>
      let left_nat := lazymatch left_count with
        | Z.of_nat ?count => constr:(count)
        | _ => eval cbn in (Z.to_nat left_count)
        end in
      let right_nat := lazymatch right_count with
        | Z.of_nat ?count => constr:(count)
        | _ => eval cbn in (Z.to_nat right_count)
        end in
      solve [eapply (zesu_pack_decoded_slices width left_nat right_nat bytes
        left_value right_value); [lia | eassumption | eassumption]]
  end.
