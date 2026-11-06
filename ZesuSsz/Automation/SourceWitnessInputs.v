Require Import isla.riscv64.riscv64.
Require Import isla.automation.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessSelector.
Require Import ZesuSsz.Automation.ResourceGroups.
From Coq Require Import Strings.String Lists.List.
From iris.proofmode Require Import environments.
Set Default Proof Mode "Classic".

Class ZesuStepSourceWitnesses : Prop := zesu_step_source_witnesses : True.

(* These markers retain values. They assert no property of those values. *)
Inductive ZesuSourceWitness {A : Type} (key : string) (value : A) : Prop :=
  ZesuSourceWitnessHere : ZesuSourceWitness key value.

Inductive ZesuSourceInput : Type -> Type :=
  | ZesuSourceUnit : ZesuSourceInput unit
  | ZesuSourceRegister (width : N) (register : string) : ZesuSourceInput (bv width)
  | ZesuSourceValue (A : Type) (key : string) : ZesuSourceInput A
  | ZesuSourcePair {A B : Type} :
      ZesuSourceInput A -> ZesuSourceInput B -> ZesuSourceInput (A * B).

Class ZesuEntrySourceWitnessMapping {Key : Type} (key : Key) (Input Witness : Type) := {
  zesu_source_witness_input : ZesuSourceInput Input;
  zesu_source_witness_mapping : Input -> Witness
}.
#[global] Hint Mode ZesuEntrySourceWitnessMapping + + - - : typeclass_instances.

Inductive ZesuSourceOwnerPlan : Type :=
  | ZesuSourceOwnerEnd : ZesuSourceOwnerPlan
  | ZesuSourceOwnerSlot (A : Type) (key : option string)
      (remaining : ZesuSourceOwnerPlan) : ZesuSourceOwnerPlan.

Class ZesuSourceOwner {Sigma : gFunctors} (source : iProp Sigma)
    (plan : ZesuSourceOwnerPlan) := {
  zesu_source_owner_original : iProp Sigma;
  zesu_source_owner_original_eq : source = zesu_source_owner_original
}.
#[global] Hint Mode ZesuSourceOwner + + - : typeclass_instances.

Class ZesuSourceDeclaration (pc : bv 64) (variable : Z) (width : N)
    (key : string) : Prop := zesu_source_declaration : True.
#[global] Hint Mode ZesuSourceDeclaration + + + - : typeclass_instances.

Ltac zesu_read_source_value wanted key continuation :=
  EntryWitnessInputs.zesu_witness_resolved key;
  let first := match goal with
    | Hsource : @ZesuSourceWitness ?T key ?value |- _ => constr:(Hsource)
    end in
  let last := match reverse goal with
    | Hsource : @ZesuSourceWitness ?T key ?value |- _ => constr:(Hsource)
    end in
  tryif constr_eq first last then idtac
  else fail 100 "The source witness projection is ambiguous.";
  lazymatch type of first with
  | @ZesuSourceWitness ?actual_type _ ?value =>
      constr_eq actual_type wanted;
      EntryWitnessInputs.zesu_witness_resolved value;
      continuation value
  end.

Ltac zesu_read_source_input source continuation :=
  let source := eval hnf in source in
  lazymatch source with
  | ZesuSourceUnit => continuation constr:(tt)
  | ZesuSourceRegister ?width ?register =>
      EntryWitnessInputs.zesu_witness_read_input
        constr:(ZesuWitnessRegister width register) continuation
  | ZesuSourceValue ?T ?key => zesu_read_source_value T key continuation
  | @ZesuSourcePair ?A ?B ?left ?right =>
      zesu_read_source_input left ltac:(fun first =>
        zesu_read_source_input right ltac:(fun second =>
          continuation constr:((first, second))))
  end.

Ltac zesu_capture_source_slots name source plan :=
  let plan := eval hnf in plan in
  lazymatch plan with
  | ZesuSourceOwnerEnd =>
      lazymatch source with
      | @bi_exist _ _ _ => fail 100 "The source package has an extra witness."
      | _ => idtac
      end
  | ZesuSourceOwnerSlot ?expected ?key ?remaining =>
      lazymatch source with
      | @bi_exist _ ?actual ?body =>
          constr_eq actual expected;
          let value := fresh "source_value" in
          iDestruct name as (value) name;
          lazymatch key with
          | Some ?identity =>
              let marker := fresh "HsourceWitness" in
              pose (marker := @ZesuSourceWitnessHere expected identity value)
          | None => idtac
          end;
          let rest := eval cbv beta in (body value) in
          zesu_capture_source_slots name rest remaining
      | _ => fail 100 "The source package is missing a witness."
      end
  end.

(* The owner registration fixes the complete source package before unfolding. *)
Ltac zesu_capture_source_owner_hyp :=
  iMatchHyp ltac:(fun name source =>
    let registration := constr:(_ : ZesuSourceOwner source _) in
    let instance_head := get_head registration in
    let original := eval cbv beta iota delta
      [zesu_source_owner_original instance_head] in
      (@zesu_source_owner_original _ source _ registration) in
    let source_head := get_head source in
    let original_head := get_head original in
    constr_eq source_head original_head;
    lazymatch type of registration with
    | ZesuSourceOwner _ ?plan =>
        let expanded := eval cbv beta delta [source_head] in source in
        progress iEval (unfold source_head) in name;
        zesu_capture_source_slots name expanded plan
    end).

(* Capture the registered package before wand unfolding exposes its binders. *)
Ltac zesu_capture_source_owner_wand :=
  lazymatch goal with
  | |- envs_entails _ (bi_wand ?source _) =>
      let registration := constr:(_ : ZesuSourceOwner source _) in
      let instance_head := get_head registration in
      let original := eval cbv beta iota delta
        [zesu_source_owner_original instance_head] in
        (@zesu_source_owner_original _ source _ registration) in
      let source_head := get_head source in
      let original_head := get_head original in
      constr_eq source_head original_head;
      li_unfold_lets_in_context;
      let name := iFresh in
      iIntros name;
      zesu_capture_source_owner_hyp;
      ResourceGroups.zesu_open_resource_groups
  end.

Ltac zesu_capture_source_owner :=
  first [zesu_capture_source_owner_wand | zesu_capture_source_owner_hyp].

Ltac zesu_source_mapping_capture key :=
  EntryWitnessInputs.zesu_witness_resolved key;
  tryif (match goal with _ : ZesuEntryWitnessPending key _ |- _ => idtac end)
  then fail 0 "The successor already has a pending source mapping." else idtac;
  let registration := constr:(_ : ZesuEntrySourceWitnessMapping key _ _) in
  lazymatch type of registration with
  | @ZesuEntrySourceWitnessMapping ?Key ?registered ?Input ?Witness =>
      let requested_head := get_head key in
      let registered_head := get_head registered in
      constr_eq requested_head registered_head;
      let input := constr:(@zesu_source_witness_input Key key Input Witness registration) in
      let mapping := constr:(@zesu_source_witness_mapping Key key Input Witness registration) in
      tryif zesu_read_source_input input ltac:(fun values =>
        let data := constr:(mapping values) in
        EntryWitnessInputs.zesu_witness_resolved data;
        let marker := fresh "HentryWitnessPending" in
        pose (marker := @ZesuEntryWitnessPendingHere Key Witness key data))
      then idtac
      else fail 100 "The registered source input is not owned."
  end.

Ltac zesu_source_mapping_capture_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_sep _ ?requested _) =>
      tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved requested
      then fail 0 else zesu_source_mapping_capture requested
  | |- environments.envs_entails _ ?requested =>
      tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved requested
      then fail 0 else zesu_source_mapping_capture requested
  end.

Section DeclareSource.
Context `{!islaG Sigma} `{!threadG}.
Lemma zesu_wp_declare_source_value (key : string) variable es ann width :
  (∀ value : bv width,
      ⌜ZesuSourceWitness key value⌝ -∗
      WPasm (subst_trace (Val_Bits value) variable es))
  ⊢ WPasm (Smt (DeclareConst variable (Ty_BitVec width)) ann :t: es).
Proof.
  iIntros "Hcontinuation".
  iApply li_wp_declare_const_bv. iIntros (value).
  iApply ("Hcontinuation" $! value).
  iPureIntro. constructor.
Qed.
End DeclareSource.

(* The owned PC and declaration number select the source location before intro. *)
Ltac zesu_read_source_declaration_key pc variable width continuation :=
  is_closed_term pc;
  let address := eval vm_compute in (bv_unsigned pc) in
  let location := constr:(_ :
    ZesuSourceDeclaration (@BV 64%N address _) variable width _) in
  lazymatch type of location with
  | ZesuSourceDeclaration _ _ _ ?key =>
      EntryWitnessInputs.zesu_witness_resolved key;
      continuation key
  end.

Ltac zesu_capture_source_declaration :=
  lazymatch goal with
  | |- envs_entails _
      (WPasm (Smt (DeclareConst ?variable (Ty_BitVec ?width)) ?ann :t: ?es)) =>
      EntryWitnessInputs.zesu_witness_read_input
        constr:(ZesuWitnessRegister 64 "PC") ltac:(fun pc =>
          zesu_read_source_declaration_key pc variable width ltac:(fun key =>
              notypeclasses refine (tac_fast_apply
                (@zesu_wp_declare_source_value _ _ _ key variable es ann width) _);
              let value := fresh "source_declaration_value" in
              iIntros (value) "_";
              let marker := fresh "HsourceWitness" in
              pose (marker := @ZesuSourceWitnessHere (bv width) key value)))
  end.
