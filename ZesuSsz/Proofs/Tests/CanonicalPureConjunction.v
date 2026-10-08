Require Import ZesuSsz.Automation.All.

Module TargetRouteOff.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Section TargetRegistration.
Context {Sigma : gFunctors}.
Definition registeredGuardTarget (condition : nat -> Prop) : iProp Sigma :=
  (∃ datum : nat, ⌜condition datum⌝ ∗ True)%I.
#[local] Instance registeredGuardTarget_unfold : LithiumUnfold (@registeredGuardTarget) := I.
Local Typeclasses Opaque registeredGuardTarget.
#[local] Instance registeredGuardIntroduction condition (datum : nat) :
  ZesuPureFactAnchor (registeredGuardTarget condition) True
    (⌜condition datum⌝ ∗ True)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, registeredGuardTarget.
  iIntros "(%Hcondition & _)". iExists datum. iSplit; done.
Qed.
Lemma target_registration_off (condition : nat -> Prop) (datum : nat)
    (Hcondition : condition datum) : True ⊢ registeredGuardTarget condition.
Proof.
  iIntros "_".
  let before := match goal with |- ?goal => constr:(goal) end in
  first [zesu_target_registered_intro_if_enabled; fail 1 "unexpected route success" | idtac "RULE35_OFF_FALLBACK"];
  let after := match goal with |- ?goal => constr:(goal) end in
  constr_eq before after.
  unfold registeredGuardTarget. iExists datum. iSplit; done.
Qed.
End TargetRegistration.
End TargetRouteOff.

Module TargetRouteOn.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.Switches.CanonicalPureConjunction.
Section TargetRegistration.
Context {Sigma : gFunctors}.
Definition registeredGuardTarget (condition : nat -> Prop) : iProp Sigma :=
  (∃ datum : nat, ⌜condition datum⌝ ∗ True)%I.
#[local] Instance registeredGuardTarget_unfold : LithiumUnfold (@registeredGuardTarget) := I.
Local Typeclasses Opaque registeredGuardTarget.
#[local] Instance registeredGuardIntroduction condition (datum : nat) :
  ZesuPureFactAnchor (registeredGuardTarget condition) True
    (⌜condition datum⌝ ∗ True)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, registeredGuardTarget.
  iIntros "(%Hcondition & _)". iExists datum. iSplit; done.
Qed.
Ltac require_target_registration_fallback shared :=
  let before := match goal with |- ?goal => constr:(goal) end in
  let sharedValue := eval unfold shared in shared in
  first [zesu_target_registered_intro_if_enabled; fail 1 "unexpected route success"
        | idtac "RULE35_FALLBACK"];
  let after := match goal with |- ?goal => constr:(goal) end in
  constr_eq before after; is_evar sharedValue.
Lemma target_registration_retained_fact (condition : nat -> Prop) (datum : nat)
    (Hcondition : condition datum) : True ⊢ registeredGuardTarget condition.
Proof. iIntros "_". zesu_target_registered_intro_if_enabled. done. Qed.
Lemma target_registration_true_frame (condition : nat -> Prop) (datum : nat)
    (Hcondition : condition datum) : True ⊢ registeredGuardTarget condition ∗ True.
Proof. iIntros "_". zesu_target_registered_intro_if_enabled. done. Qed.
Lemma target_registration_conjunction (condition : nat -> Prop) (datum : nat) lo middle hi
    (Hcondition : condition datum) (Hlo : lo <= middle) (Hhi : middle <= hi) :
  True ⊢ registeredGuardTarget
    (fun selected => condition selected /\ lo <= middle /\ middle <= hi).
Proof. iIntros "_". zesu_target_registered_intro_if_enabled. done. Qed.
Lemma target_registration_reversed_hypotheses (condition : nat -> Prop) (datum : nat) lo middle hi
    (Hhi : middle <= hi) (Hlo : lo <= middle) (Hcondition : condition datum) :
  True ⊢ registeredGuardTarget
    (fun selected => condition selected /\ lo <= middle /\ middle <= hi).
Proof. iIntros "_". zesu_target_registered_intro_if_enabled. done. Qed.
Lemma target_registration_alias (condition : nat -> Prop) (datum : nat) (Hcondition : condition datum) :
  True ⊢ registeredGuardTarget condition.
Proof.
  iIntros "_".
  lazymatch goal with |- envs_entails ?environment ?target =>
    let alias := fresh "environmentAlias" in
    pose (alias := environment); change (envs_entails alias target)
  end.
  zesu_target_registered_intro_if_enabled. done.
Qed.
Lemma target_registration_registry_preserved (condition : nat -> Prop) (datum : nat)
    (Hcondition : condition datum) : True.
Proof using Sigma.
  let target := constr:(registeredGuardTarget condition) in
  let anchor := open_constr:(_ : iProp Sigma) in
  let source := open_constr:(_ : iProp Sigma) in
  assert (ZesuPureFactAnchor target anchor source) as Hbefore by
    (assert_fails typeclasses eauto; exact (registeredGuardIntroduction condition datum)).
  clear Hbefore.
  let target := constr:(registeredGuardTarget condition) in
  let checked := zesu_closed_target_registration target in
  assert_fails (has_evar checked);
  let anchor := open_constr:(_ : iProp Sigma) in
  let source := open_constr:(_ : iProp Sigma) in
  assert (ZesuPureFactAnchor target anchor source) as Hafter by
    (assert_fails typeclasses eauto; exact (registeredGuardIntroduction condition datum)).
  exact I.
Qed.
Lemma target_registration_wrong_data (condition other : nat -> Prop)
    (wrong : nat) (Hwrong : other wrong)
    (Hproof : True ⊢ registeredGuardTarget condition) :
  True ⊢ registeredGuardTarget condition.
Proof.
  iIntros "_". evar (shared : nat).
  require_target_registration_fallback shared.
  instantiate (shared := 3). iApply Hproof. done.
Qed.
Lemma target_registration_unresolved_data
    (Hproof : True ⊢ registeredGuardTarget (fun _ : nat => Coq.Init.Logic.True)) :
  True ⊢ registeredGuardTarget (fun _ : nat => Coq.Init.Logic.True).
Proof.
  iIntros "_". evar (shared : nat).
  require_target_registration_fallback shared.
  instantiate (shared := 3). iApply Hproof. done.
Qed.
Lemma target_registration_failed_premises_rollback (condition : nat -> Prop)
    (Hproof : True ⊢ registeredGuardTarget condition) :
  True ⊢ registeredGuardTarget condition.
Proof.
  iIntros "_". evar (shared : nat).
  require_target_registration_fallback shared.
  instantiate (shared := 3). iApply Hproof. done.
Qed.
Definition unregisteredGuardTarget (condition : nat -> Prop) : iProp Sigma :=
  (∃ datum : nat, ⌜condition datum⌝ ∗ False)%I.
#[local] Instance unregisteredGuardTarget_unfold : LithiumUnfold (@unregisteredGuardTarget) := I.
Local Typeclasses Opaque unregisteredGuardTarget.
Lemma target_registration_absent_registration (condition : nat -> Prop)
    (Hproof : True ⊢ unregisteredGuardTarget condition) :
  True ⊢ unregisteredGuardTarget condition.
Proof.
  iIntros "_". evar (shared : nat).
  require_target_registration_fallback shared.
  instantiate (shared := 3). iApply Hproof. done.
Qed.
Lemma target_registration_shared_evar (condition : nat -> Prop) (datum : nat)
    (Hcondition : condition datum) : True.
Proof.
  evar (shared : nat).
  let sharedValue := eval unfold shared in shared in
  let checked := zesu_closed_target_registration
    constr:(registeredGuardTarget condition) in
  assert_fails (has_evar checked); is_evar sharedValue.
  instantiate (shared := 3). exact I.
Qed.
End TargetRegistration.
End TargetRouteOn.

Module TargetRouteGroups.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.Switches.CanonicalPureConjunction.
Section TargetRegistration.
Context {Sigma : gFunctors}.
Definition registeredGuardTarget (condition : nat -> Prop) : iProp Sigma :=
  (∃ datum : nat, ⌜condition datum⌝ ∗ True)%I.
#[local] Instance registeredGuardTarget_unfold : LithiumUnfold (@registeredGuardTarget) := I.
Local Typeclasses Opaque registeredGuardTarget.
#[local] Instance registeredGuardIntroduction condition (datum : nat) :
  ZesuPureFactAnchor (registeredGuardTarget condition) True
    (⌜condition datum⌝ ∗ True)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, registeredGuardTarget.
  iIntros "(%Hcondition & _)". iExists datum. iSplit; done.
Qed.
Definition unregisteredGuardTarget (condition : nat -> Prop) : iProp Sigma :=
  (∃ datum : nat, ⌜condition datum⌝ ∗ False)%I.
#[local] Instance unregisteredGuardTarget_unfold : LithiumUnfold (@unregisteredGuardTarget) := I.
Local Typeclasses Opaque unregisteredGuardTarget.
Lemma target_registration_failed_source_groups (condition : nat -> Prop)
    (Hproof : True ⊢ registeredGuardTarget condition) :
  (True ⊢ registeredGuardTarget condition) /\ True.
Proof.
  split. 2: shelve. iIntros "_". evar (shared : nat).
  let before := match goal with |- ?goal => constr:(goal) end in
  let sharedValue := eval unfold shared in shared in
  first [zesu_target_registered_intro_if_enabled; fail 1 "unexpected route success" | idtac "RULE35_FALLBACK"];
  let after := match goal with |- ?goal => constr:(goal) end in
  constr_eq before after; is_evar sharedValue.
  instantiate (shared := 3). iApply Hproof. done.
  Unshelve. exact I.
Qed.
Lemma target_registration_failed_lookup_groups (condition : nat -> Prop)
    (Hproof : True ⊢ unregisteredGuardTarget condition) :
  (True ⊢ unregisteredGuardTarget condition) /\ True.
Proof.
  split. 2: shelve. iIntros "_". evar (shared : nat).
  let before := match goal with |- ?goal => constr:(goal) end in
  let sharedValue := eval unfold shared in shared in
  first [zesu_target_registered_intro_if_enabled; fail 1 "unexpected route success" | idtac "RULE35_FALLBACK"];
  let after := match goal with |- ?goal => constr:(goal) end in
  constr_eq before after; is_evar sharedValue.
  instantiate (shared := 3). iApply Hproof. done.
  Unshelve. exact I.
Qed.
Definition registeredNestedTarget (firstCondition secondCondition : nat -> Prop) : iProp Sigma :=
  (∃ firstDatum : nat, ∃ secondDatum : nat,
    ⌜firstCondition firstDatum /\ secondCondition secondDatum⌝ ∗ True)%I.
#[local] Instance registeredNestedTarget_unfold : LithiumUnfold (@registeredNestedTarget) := I.
Local Typeclasses Opaque registeredNestedTarget.
#[local] Instance registeredNestedIntroduction firstCondition secondCondition firstDatum secondDatum :
  ZesuPureFactAnchor (registeredNestedTarget firstCondition secondCondition) True
    (⌜firstCondition firstDatum /\ secondCondition secondDatum⌝ ∗ True)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, registeredNestedTarget.
  iIntros "(%Hconditions & _)". iExists firstDatum, secondDatum. iSplit; done.
Qed.
Lemma target_registration_current_nested (firstCondition secondCondition : nat -> Prop) (firstDatum secondDatum : nat)
    (Hfirst : firstCondition firstDatum) (Hsecond : secondCondition secondDatum) :
  True ⊢ registeredNestedTarget firstCondition secondCondition.
Proof. iIntros "_". zesu_target_registered_intro_if_enabled. done. Qed.
Definition registeredRelationAlias (firstCondition secondCondition : nat -> Prop)
    (firstDatum secondDatum : nat) : Prop :=
  firstCondition firstDatum /\ secondCondition secondDatum.
Lemma target_registration_relation_alias (firstCondition secondCondition : nat -> Prop) (firstDatum secondDatum : nat)
    (Hconditions : registeredRelationAlias firstCondition secondCondition firstDatum secondDatum) :
  True ⊢ registeredNestedTarget firstCondition secondCondition.
Proof.
  iIntros "_". zesu_target_registered_intro_if_enabled. done.
Qed.
End TargetRegistration.
End TargetRouteGroups.

Lemma target_registration_checked_exports : True.
Proof.
  Check TargetRouteOff.target_registration_off.
  Check TargetRouteOn.target_registration_retained_fact.
  Check TargetRouteOn.target_registration_true_frame.
  Check TargetRouteOn.target_registration_conjunction.
  Check TargetRouteOn.target_registration_reversed_hypotheses.
  Check TargetRouteOn.target_registration_alias.
  Check TargetRouteOn.target_registration_registry_preserved.
  Check TargetRouteOn.target_registration_wrong_data.
  Check TargetRouteOn.target_registration_unresolved_data.
  Check TargetRouteOn.target_registration_failed_premises_rollback.
  Check TargetRouteOn.target_registration_absent_registration.
  Check TargetRouteOn.target_registration_shared_evar.
  Check TargetRouteGroups.target_registration_failed_source_groups.
  Check TargetRouteGroups.target_registration_failed_lookup_groups.
  Check TargetRouteGroups.target_registration_current_nested.
  Check TargetRouteGroups.target_registration_relation_alias.
  exact I.
Qed.
