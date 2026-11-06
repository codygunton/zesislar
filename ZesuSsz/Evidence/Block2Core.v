Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith NArith.NArith micromega.Lia.
Require Import stdpp.bitvector.definitions.
From stdpp Require Import tactics.
From iris.proofmode Require Import environments.

Ltac block2_has_unresolved term :=
  first [has_evar term |
    multimatch goal with
    | local := ?body : _ |- _ =>
        lazymatch term with
        | context[local] => block2_has_unresolved body
        end
    end].

Ltac block2_fixed term :=
  assert_fails ltac:(block2_has_unresolved term).

Ltac block2_closed term :=
  block2_fixed term;
  is_closed_term term.

Ltac block2_arithmetic proposition :=
  lazymatch proposition with
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | Z.ge _ _ => idtac
  | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac
  end.

(* This projection runs only inside the proof of a required range. *)
Ltac block2_range_context :=
  repeat match goal with
  | hypothesis : ?proposition |- _ =>
      lazymatch type of proposition with Prop => idtac end;
      let expanded := eval hnf in proposition in
      lazymatch expanded with
      | _ /\ _ => change expanded in hypothesis; destruct hypothesis
      end
  end;
  repeat multimatch goal with
  | hypothesis : ?proposition |- _ =>
      block2_arithmetic proposition;
      multimatch proposition with
      | context[?term] =>
          lazymatch type of term with Z => idtac end;
          block2_closed term;
          let reduced := eval vm_compute in term in
          progress (change_no_check term with reduced in hypothesis)
      end
  end.

Ltac block2_cast width cast_width value continuation :=
  constr_eq width cast_width;
  block2_closed width;
  block2_fixed value;
  let modulus := eval vm_compute in (bv_modulus width) in
  let range := fresh "Hblock2Range" in
  assert (range : (0 <= value < bv_modulus width)%Z) by
    (first [assumption |
      block2_range_context;
      change (0 <= value < modulus)%Z;
      lia]);
  let equality := constr:(Z_to_bv_small width value range) in
  continuation equality;
  clear range.

Ltac block2_pointer_step :=
  first [
    multimatch goal with
    | hypothesis : ?proposition |- _ =>
        block2_fixed proposition;
        multimatch proposition with
        | context[@bv_unsigned ?width (Z_to_bv ?cast_width ?value)] =>
            block2_cast width cast_width value
              ltac:(fun equality => progress (rewrite equality in hypothesis))
        end
    end |
    lazymatch goal with |- ?proposition =>
      block2_fixed proposition;
      multimatch proposition with
      | context[@bv_unsigned ?width (Z_to_bv ?cast_width ?value)] =>
          block2_cast width cast_width value
            ltac:(fun equality => progress (rewrite equality))
      end
    end |
    multimatch goal with
    | hypothesis : ?proposition |- _ =>
        block2_fixed proposition;
        multimatch proposition with
        | context[@bv_add ?width ?value ?amount] =>
            block2_closed width;
            let zero := constr:((0%bv : bv width)) in
            constr_eq amount zero;
            progress (rewrite (bv_add_0_r value zero ltac:(bv_solve)) in hypothesis)
        | context[(?value + 0)%Z] => progress (rewrite (Z.add_0_r value) in hypothesis)
        end
    end |
    lazymatch goal with |- ?proposition =>
      block2_fixed proposition;
      multimatch proposition with
      | context[@bv_add ?width ?value ?amount] =>
          block2_closed width;
          let zero := constr:((0%bv : bv width)) in
          constr_eq amount zero;
          progress (rewrite (bv_add_0_r value zero ltac:(bv_solve)))
      | context[(?value + 0)%Z] => progress (rewrite (Z.add_0_r value))
      end
    end].

Ltac block2_pointer_canonicalize := repeat progress block2_pointer_step.

Ltac block2_prepare_pure :=
  lazymatch goal with
  | |- SHELVED_SIDECOND _ => prepare_sidecond
  | |- envs_entails _ _ => fail 0
  | _ => unLET; normalize_and_simpl_goal
  end.

Ltac block2_finish :=
  first [
    lazymatch goal with
    | |- envs_entails _ _ => first [solve [iAssumption] | solve [iFrame]]
    end |
    lazymatch goal with
    | |- envs_entails _ _ => fail 0
    | _ => solve [block2_prepare_pure; first [done | bv_solve]]
    end].

Ltac zesu_block2 pointer_family :=
  try iStartProof;
  unshelve (repeat first [
    lazymatch pointer_family with
    | true => progress block2_pointer_canonicalize
    end |
    liAStep]);
  try block2_prepare_pure;
  try (lazymatch pointer_family with true => block2_pointer_canonicalize end);
  try block2_finish.
