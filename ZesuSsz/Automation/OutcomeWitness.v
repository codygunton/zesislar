Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

Class ZesuStepOutcomeWitness : Prop := zesu_step_outcome_witness : True.

Ltac zesu_select_outcome_witness :=
  let _ := constr:(_ : ZesuStepOutcomeWitness) in
  match goal with
  | Hvalid : ?valid ?bytes,
    Houtcome : ?outcome ?bytes = ?result |- envs_entails _
      (@bi_exist _ (li_prod spec (li_prod (list (bv 8)) unit))
        (fun x => (⌜?required x.2ₗ⌝ ∗ _)%I)) =>
      unify valid required;
      let bytesType := type of bytes in
      unify bytesType (list (bv 8));
      iExists (_, bytes, tt)ₗ;
      iSplit; [iPureIntro; exact Hvalid |]
  end.

Ltac zesu_rewrite_selected_outcome :=
  match goal with
  | Houtcome : ?outcome ?bytes = ?result |- envs_entails _ _ =>
      progress rewrite Houtcome
  end.
