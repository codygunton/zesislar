Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteArrayAssemblyCodec.
Require Import lithium.interpreter lithium.pure_definitions.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Local Open Scope Z_scope.

Ltac zesu_memory_witness_occurs candidate expression :=
  multimatch expression with
  | context [?part] => constr_eq_strict candidate part
  end.

(* Every value is fresh. Only syntactically absent byte-vector fields get zero. *)
Ltac zesu_memory_default_unused value requested :=
  let bare := eval cbv beta iota zeta in value in
  lazymatch bare with
  | @li_pair _ _ ?head ?tail =>
      zesu_memory_default_unused head requested;
      zesu_memory_default_unused tail requested
  | tt => idtac
  | _ =>
      is_evar bare;
      let T := type of bare in
      lazymatch T with
      | bv ?width =>
          tryif zesu_memory_witness_occurs bare requested then idtac
          else unify bare (Z_to_bv width 0)
      end
  end.

Ltac zesu_memory_open_tuple fuel :=
  lazymatch fuel with
  | S ?remaining =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
          let witness := Hooks.zesu_constraint_witness T in
          let requested := eval cbv beta iota zeta delta [li_fst li_snd]
            in (body witness) in
          zesu_memory_default_unused witness requested;
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod;
          zesu_memory_open_tuple remaining
      | _ => idtac
      end
  | O => fail 0 "The memory package exceeds its existential step bound."
  end.

(* Scalar constraints select constrained fields. The array consumer preserves
   the source addresses, fractions, and byte order. Callers supply pure logic. *)
Ltac zesu_memory_tuple consume_facts finish :=
  ResourceGroups.zesu_open_resource_groups;
  repeat multimatch goal with
  | Hwidth : (8 = ?stride * 8)%N |- _ =>
      is_var stride;
      let Hone := fresh "HmemoryByteStride" in
      assert (Hone : stride = 1%N) by (clear - Hwidth; Lia.lia);
      subst stride
  end;
  zesu_memory_open_tuple constr:(16%nat);
  repeat iMatchHyp ltac:(fun name body => is_var body; progress (iFrame name));
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_sep _ (isla.ghost_state.mem_mapsto_array_def _ _ _) _) =>
      iSplitL;
      [rewrite <- isla.ghost_state.mem_mapsto_array_eq;
       ByteArrayAssemblyCodec.zesu_byte_array_assemble_codec | idtac]
  end;
  lazymatch goal with
  | |- environments.envs_entails _ ?requested => consume_facts requested
  end;
  finish constr:(tt).
