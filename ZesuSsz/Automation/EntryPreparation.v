Require Import ZesuSsz.Automation.CallSet.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import InstrSpecs.Lookup.
From iris.proofmode Require Import environments tactics intro_patterns.

(* Prepare a selected entry before execution shelves its side conditions.
   Select only a package with a leading conjunction fact. The forall/True
   probe checks an existential body without an assumption or a witness.
   Open registered companions only inside that selected package. Protect
   primitive resources and declared seals before any reduction. *)
Ltac zesu_entry_assertion_protected assertion :=
  let head := get_head assertion in
  first [
    constr_eq head constr:(@mem_mapsto_array) |
    constr_eq head constr:(@mem_mapsto) |
    constr_eq head constr:(@mem_mapsto_uninit) |
    constr_eq head constr:(@reg_col) |
    constr_eq head constr:(@reg_mapsto) |
    constr_eq head constr:(@instr) |
    constr_eq head constr:(@instr_body) |
    constr_eq head constr:(@instr_pre) |
    constr_eq head constr:(@instr_lookup_resources) |
    constr_eq head constr:(@instr_body_lookup_resources) |
    constr_eq head constr:(@spec_trace) |
    constr_eq head constr:(@mmio_range) |
    let _ := constr:(_ : ZesuSealed assertion _ _ _) in idtac |
    let _ := constr:(_ : ZesuSealedOpaqueTail assertion _) in idtac |
    lazymatch assertion with
    | @bi_pure _ _ => fail
    | _ => let _ := constr:(_ : Persistent assertion) in idtac
    end ].

Ltac zesu_entry_fact_shape assertion :=
  tryif zesu_entry_assertion_protected assertion then fail else
  first [
    lazymatch assertion with
    | @bi_pure _ ?fact =>
        let folded := eval hnf in fact in
        lazymatch folded with _ /\ _ => idtac end
    | @bi_sep _ ?left ?right =>
        zesu_entry_fact_shape left
    | @bi_exist _ ?T ?body =>
        let check := fresh "entryFactCheck" in
        assert (forall probe : T, True) as check by
          (let probe := fresh "entryProbe" in intro probe;
           let candidate := eval cbv beta in (body probe) in
           zesu_entry_fact_shape candidate; exact I);
        clear check
    end
  | let next := eval red in assertion in
    tryif constr_eq next assertion then fail else
    zesu_entry_fact_shape next ].

Ltac zesu_entry_has_pure_fact assertion :=
  tryif has_evar assertion then fail else zesu_entry_fact_shape assertion.

Ltac zesu_unfold_entry_head H assertion :=
  lazymatch assertion with
  | ?function ?argument => zesu_unfold_entry_head H function
  | _ => iEval (unfold assertion) in H
  end.

Ltac zesu_expand_selected_entry H :=
  let entry := iTypeOf H in
  lazymatch entry with Some (_, ?P) =>
    tryif has_evar P then fail else
    tryif zesu_entry_assertion_protected P then idtac else
    first [
      lazymatch P with
      | @bi_exist _ _ _ =>
          iDestruct H as (?) H; zesu_expand_selected_entry H
      | @bi_sep _ _ _ =>
          let left := iFresh in let right := iFresh in
          let pattern := constr:(IList ((IIdent left :: IIdent right :: nil) :: nil)) in
          iDestruct H as pattern;
          zesu_expand_selected_entry left; zesu_expand_selected_entry right
      | @bi_pure _ _ => iDestruct H as "%"
      | @reg_mapsto_pred _ _ _ _ _ _ =>
          iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in H;
          zesu_expand_selected_entry H
      end
    | let head := get_head P in
      let _ := constr:(_ : LithiumUnfold head) in
      let reduced := eval red in P in
      tryif constr_eq reduced P then fail else
      zesu_unfold_entry_head H P; zesu_expand_selected_entry H
    | idtac ]
  end.

Ltac zesu_prepare_entry_facts :=
  zesu_call_set_on;
  lazymatch goal with |- envs_entails _ (WPasm _) => idtac end;
  first [
    iMatchHyp ltac:(fun H P =>
      tryif has_evar P then fail else
      tryif zesu_entry_assertion_protected P then fail else
      lazymatch P with
      | @bi_pure _ _ => iDestruct H as "%"; try iClear H
      end)
  | iMatchHyp ltac:(fun H P =>
      zesu_entry_has_pure_fact P;
      first [
        lazymatch P with
        | @bi_exist _ _ _ => zesu_expand_selected_entry H
        | @bi_sep _ _ _ => zesu_expand_selected_entry H
        | @bi_pure _ _ => zesu_expand_selected_entry H
        end
      | zesu_unfold_entry_head H P; zesu_expand_selected_entry H ])
  | progress zesu_witness_facts
  | match goal with H : _ /\ _ |- _ => destruct H end ].
