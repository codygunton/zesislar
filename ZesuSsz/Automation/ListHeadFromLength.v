From Coq Require Import List ZArith Bool.
From stdpp Require Import bitvector.definitions.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zesu_list_head_from_cast_length {A : Type} (bytes : list A)
    (default : A) (width : N) (quantity : Z) (zero : bv width) :
  quantity = Z.of_nat (List.length bytes) ->
  bv_unsigned zero = 0 ->
  Z_to_bv width quantity <> zero ->
  bytes = List.nth 0 bytes default :: List.skipn 1 bytes.
Proof.
  intros Hlength Hzero Hnonzero.
  destruct bytes as [|head tail]; [|reflexivity].
  cbn in Hlength. subst quantity.
  exfalso. apply Hnonzero. apply bv_eq.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_0.
  symmetry. exact Hzero.
Qed.

Ltac zesu_list_head_from_length :=
  lazymatch goal with
  | |- ?bytes = List.nth 0 ?bytes ?default :: List.skipn 1 ?bytes =>
    let finish width quantity zero nonzero :=
      solve [eapply (zesu_list_head_from_cast_length bytes default width quantity zero);
        [eassumption | reflexivity | exact nonzero]] in
    first
      [ match goal with
        | Hlength : ?quantity = Z.of_nat (List.length bytes),
          Hnonzero : Z_to_bv ?width ?quantity <> ?zero |- _ =>
            finish width quantity zero Hnonzero
        end
      | match goal with
        | Hlength : ?quantity = Z.of_nat (List.length bytes),
          Hguard : negb (bool_decide (Z_to_bv ?width ?quantity = ?zero)) = true |- _ =>
            let nonzero := fresh "HheadNonzero" in
            pose proof Hguard as nonzero;
            apply Bool.negb_true_iff in nonzero;
            apply bool_decide_eq_false_1 in nonzero;
            finish width quantity zero nonzero
        end ]
  end.
