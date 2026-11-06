Require Export ZesuSsz.Automation2.ExplicitWitnesses292.
From lithium Require Import interpreter base pure_definitions.
From iris.proofmode Require Import environments.
Set Default Proof Mode "Classic".

Ltac zesu_reverse_witness_spine293 data accumulated continuation :=
  let spine := eval hnf in data in
  lazymatch spine with
  | @pair _ _ ?value ?remaining =>
      zesu_reverse_witness_spine293 remaining constr:((value, accumulated)) continuation
  | tt => continuation accumulated
  | _ => fail 1 "The substitution is not a product spine."
  end.

(* Stock liExist prepends each later declaration to the internal li_prod. *)
Ltac zesu_apply_lithium_witnesses data :=
  tryif has_evar data then fail 1 "The explicit substitution contains an evar." else idtac;
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
      tryif has_evar body then fail 1 "The target assertion contains an evar." else idtac;
      zesu_reverse_witness_spine293 data constr:(tt) ltac:(fun internal =>
        zesu_explicit_tuple292 constr:(li_prod A B) internal
          ltac:(fun witness remaining =>
            let tail := eval hnf in remaining in
            lazymatch tail with
            | tt =>
                let instantiated := eval cbv beta iota delta [li_fst li_snd] in (body witness) in
                lazymatch instantiated with
                | @bi_exist _ _ _ => fail 1 "The target is only partially grouped."
                | _ => zesu_apply_explicit_witnesses internal
                end
            | _ => fail 1 "The substitution contains an extra witness."
            end))
  | _ => fail 1 "The target is not a stock-grouped Lithium existential."
  end.
