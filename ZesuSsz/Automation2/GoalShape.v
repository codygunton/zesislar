(** Goal-shape guards of the search chains (dispatch set A).

   An alternative of `Hooks.zesu_liAStep` or `Finish.zesu_run_pass_v1` that
   can only succeed on goals of a given head runs behind a test of that head;
   the order of the alternatives is unchanged. The chains classify the goal
   once per entry (`zesu_goal_class`) and test the class with a `lazymatch`.
   Each guard is either exact by the guarded alternative's own first match, or
   relies on a stated policy of the generated statements:
   - R: an entry or source mapping key is not a Lithium judgement, a tuple
     existential, `∀`, a wand, `∧` or a bare register or memory atom;
   - R': a registered pure-fact target is not headed by `∗` either;
   - B: Lithium existential bodies are beta-normal (`fun _ => …`);
   - Z: the tag-bound closer runs only on `Z.lt` or comparison goals. *)

From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.InstrPre.

Inductive ZesuGoalClass : Set :=
| ZGwp_read | ZGwp_write | ZGwp_assert | ZGwp
| ZGfind_mem | ZGfind_instr | ZGfind_reg | ZGfind_sreg | ZGfind
| ZGsubsume | ZGlitac | ZGletbind | ZGwpaexp
| ZGex_prod | ZGex | ZGall | ZGwand | ZGand
| ZGsep_pure | ZGsep_ex | ZGsep
| ZGpure | ZGname | ZGprod | ZGprop.

(* One syntactic classification of the goal by its head. *)
Ltac zesu_goal_class :=
  lazymatch goal with
  | |- environments.envs_entails _ ?P =>
    lazymatch P with
    | WPasm ?t =>
        lazymatch t with
        | ReadMem _ _ _ _ _ _ :t: _ => constr:(ZGwp_read)
        | WriteMem _ _ _ _ _ _ _ :t: _ => constr:(ZGwp_write)
        | Smt (Assert _) _ :t: _ => constr:(ZGwp_assert)
        | _ => constr:(ZGwp)
        end
    | find_in_context ?f _ =>
        lazymatch f with
        | FindMemMapsTo _ => constr:(ZGfind_mem)
        | FindInstrKind _ _ => constr:(ZGfind_instr)
        | FindRegMapsTo _ => constr:(ZGfind_reg)
        | FindStructRegMapsTo _ _ => constr:(ZGfind_sreg)
        | _ => constr:(ZGfind)
        end
    | subsume _ _ _ => constr:(ZGsubsume)
    | li_tactic _ _ => constr:(ZGlitac)
    | let_bind_hint _ _ => constr:(ZGletbind)
    | wp_a_exp _ _ => constr:(ZGwpaexp)
    | @bi_exist _ ?A _ =>
        lazymatch A with
        | li_prod _ _ => constr:(ZGex_prod)
        | _ => constr:(ZGex)
        end
    | @bi_forall _ _ _ => constr:(ZGall)
    | @bi_wand _ _ _ => constr:(ZGwand)
    | @bi_and _ _ _ => constr:(ZGand)
    | @bi_pure _ _ => constr:(ZGpure)
    | @bi_sep _ ?l _ =>
        lazymatch l with
        | @bi_pure _ _ => constr:(ZGsep_pure)
        | @bi_exist _ _ _ => constr:(ZGsep_ex)
        | _ => constr:(ZGsep)
        end
    | _ => constr:(ZGname)
    end
  | |- forall _ : _, _ => constr:(ZGprod)
  | |- _ => constr:(ZGprop)
  end.

(* `iMatchHyp` matches `Esnoc _ ?x ?P` in the conclusion: with the environment
   behind a local name (Lithium's let_bind_envs) the conclusion holds none.
   Succeeds unless the goal is an entailment on a local-name environment. *)
Ltac zesu_env_literal :=
  lazymatch goal with
  | |- environments.envs_entails ?e _ => tryif is_var e then fail else idtac
  | |- _ => idtac
  end.

(* The environment is a literal `Envs _ _ _` record. *)
Ltac zesu_envs_record :=
  lazymatch goal with
  | |- environments.envs_entails (environments.Envs _ _ _) _ => idtac
  end.

(* Policy R: a mapping key is an entry-level proposition. *)
Ltac zesu_mapping_key_ok key :=
  lazymatch key with
  | WPasm _ => fail
  | find_in_context _ _ => fail
  | subsume _ _ _ => fail
  | li_tactic _ _ => fail
  | let_bind_hint _ _ => fail
  | wp_a_exp _ _ => fail
  | @bi_exist _ (li_prod _ _) _ => fail
  | @bi_forall _ _ _ => fail
  | @bi_wand _ _ _ => fail
  | @bi_and _ _ _ => fail
  | @reg_mapsto _ _ _ _ _ _ => fail
  | @struct_reg_mapsto _ _ _ _ _ _ _ => fail
  | @reg_col _ _ _ _ => fail
  | @mem_mapsto _ _ _ _ _ _ => fail
  | @mem_mapsto_array _ _ _ _ _ _ => fail
  | @mem_mapsto_uninit _ _ _ _ _ => fail
  | @isla.ghost_state.mem_mapsto_array_def _ _ _ _ _ _ => fail
  | _ => idtac
  end.

(* Policy R': a pure-fact key is not headed by `∗` either. *)
Ltac zesu_pure_fact_key_ok key :=
  lazymatch key with
  | @bi_sep _ _ _ => fail
  | _ => zesu_mapping_key_ok key
  end.

(* Policy B: the instruction-precondition match runs on `zesu_instr_pre_match`
   or on an existential whose body is that match (or not a `fun`). *)
Ltac zesu_instr_pre_match_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ ?body) =>
      lazymatch body with
      | (fun _ => zesu_instr_pre_match _ _ _) => idtac
      | (fun _ => _) => fail
      | _ => idtac
      end
  | |- environments.envs_entails _ (zesu_instr_pre_match _ _ _) => idtac
  end.

(* Policy Z: the tag-bound closer concludes `_ < _` in `Z`. *)
Ltac zesu_tag_bound_goal :=
  lazymatch goal with
  | |- Z.lt _ _ => idtac
  | |- @eq comparison _ _ => idtac
  end.
