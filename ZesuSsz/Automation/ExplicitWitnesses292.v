Require Import isla.riscv64.riscv64.
From lithium Require Import interpreter base pure_definitions.
From iris.proofmode Require Import environments.
Set Default Proof Mode "Classic".

Ltac zesu_explicit_uncons292 data continuation :=
  let spine := eval hnf in data in
  lazymatch spine with
  | @pair _ _ ?value ?remaining => continuation value remaining
  | tt => fail 1 "The substitution is missing a witness."
  | _ => fail 1 "The substitution is not a product spine."
  end.

Ltac zesu_explicit_type292 wanted value continuation :=
  tryif has_evar wanted then fail 1 "The target witness type is unresolved." else idtac;
  let actual := type of value in
  tryif has_evar actual then fail 1 "The supplied witness type is unresolved." else idtac;
  tryif unify actual wanted then continuation value
  else fail 1 "The supplied witness has the wrong type." actual wanted.

Ltac zesu_explicit_tuple292 tuple_type data continuation :=
  lazymatch tuple_type with
  | li_prod ?first_type ?remaining_type =>
      zesu_explicit_uncons292 data ltac:(fun value remaining =>
        zesu_explicit_type292 first_type value ltac:(fun checked =>
          zesu_explicit_tuple292 remaining_type remaining
            ltac:(fun tail rest =>
              continuation constr:(li_pair checked tail) rest)))
  | unit => continuation constr:(tt) data
  | _ => fail 1 "The Lithium witness tuple must end in unit."
  end.

Ltac zesu_explicit_take292 witness_type data continuation :=
  lazymatch witness_type with
  | li_prod _ _ => zesu_explicit_tuple292 witness_type data continuation
  | _ => zesu_explicit_uncons292 data ltac:(fun value remaining =>
      zesu_explicit_type292 witness_type value
        ltac:(fun checked => continuation checked remaining))
  end.

Ltac zesu_explicit_validate292 data requested :=
  lazymatch requested with
  | @bi_exist _ ?witness_type ?body =>
      zesu_explicit_take292 witness_type data
        ltac:(fun value remaining =>
          let instantiated := eval cbv beta iota delta [li_fst li_snd] in (body value) in
          zesu_explicit_validate292 remaining instantiated)
  | _ =>
      let tail := eval hnf in data in
      lazymatch tail with
      | tt => idtac
      | _ => fail 1 "The substitution contains an extra witness."
      end
  end.

Ltac zesu_explicit_introduce292 data :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ ?witness_type _) =>
      zesu_explicit_take292 witness_type data ltac:(fun value remaining =>
        notypeclasses refine (tac_ex_evar _ value _ _);
        red_li_prod;
        zesu_explicit_introduce292 remaining)
  | _ => idtac
  end.

Ltac zesu_apply_explicit_witnesses data :=
  tryif has_evar data then fail 1 "The explicit substitution contains an evar." else idtac;
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      tryif has_evar requested then fail 1 "The target assertion contains an evar." else idtac;
      lazymatch requested with
      | @bi_exist _ _ _ =>
          zesu_explicit_validate292 data requested;
          zesu_explicit_introduce292 data
      | _ => fail 1 "The target has no open existential."
      end
  | _ => fail 1 "The target is not an Iris entailment."
  end.
