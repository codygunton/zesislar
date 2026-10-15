Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.EntryIntro.

Module RegisteredSource.
Section Controls.
Context {Sigma : gFunctors}.
Definition entrySource (fact : Prop) (resource : iProp Sigma) : iProp Sigma :=
  (⌜fact⌝ ∗ resource)%I.
#[local] Instance : LithiumUnfold (@entrySource) := I.
Local Typeclasses Opaque entrySource.
#[local] Instance source_introduction fact resource :
    ZesuEntryIntro (entrySource fact resource) fact.
Proof. unfold ZesuEntryIntro, entrySource. iIntros "[%Hfact _]". done. Qed.

Lemma entry_intro_reordered (fact : Prop) (resource peer : iProp Sigma) :
    peer ∗ entrySource fact resource ⊢ ⌜fact⌝ ∗ peer ∗ entrySource fact resource.
Proof.
  iIntros "[Hpeer Hsource]". zesu_entry_intro_if_enabled.
  match goal with _ : fact |- _ => idtac end.
  assert_fails zesu_entry_intro_if_enabled.
  iFrame "Hpeer Hsource". done.
Qed.

Lemma entry_intro_no_duplication (fact : Prop) (resource peer : iProp Sigma)
    (Hfact : fact) :
    entrySource fact resource ∗ peer ⊢ entrySource fact resource ∗ peer.
Proof.
  iIntros "[Hsource Hpeer]". zesu_entry_intro_if_enabled.
  match goal with Hnew : fact |- _ => constr_eq Hnew Hfact end.
  assert_fails zesu_entry_intro_if_enabled.
  iFrame "Hsource Hpeer".
Qed.
Lemma entry_intro_recorded_instance (fact : Prop) (resource peer : iProp Sigma) :
    entrySource fact resource ∗ peer ⊢ entrySource fact resource ∗ peer.
Proof.
  iIntros "[Hsource Hpeer]". zesu_entry_intro_if_enabled.
  match goal with
  | _ : @ZesuEntryIntroApplied Sigma (entrySource fact resource) fact ?applied |- _ =>
      let expected := constr:(source_introduction fact resource) in
      constr_eq applied expected
  end.
  assert (additional : ZesuEntryIntro (entrySource fact resource) (fact /\ fact)).
  { unfold ZesuEntryIntro, entrySource. iIntros "[%Hfact _]". done. }
  let original := match goal with |- ?target => constr:(target) end in
  pose (savedTarget := original).
  Fail zesu_entry_intro_if_enabled.
  let original := eval unfold savedTarget in savedTarget in
  let current := match goal with |- ?target => constr:(target) end in
  constr_eq original current. clear savedTarget. iFrame "Hsource Hpeer".
Qed.
Definition designedEntry (fact : Prop) (resource : iProp Sigma) : iProp Sigma :=
  (entrySource fact resource ∗ True)%I.
#[local] Instance : LithiumUnfold (@designedEntry) := I.
Local Typeclasses Opaque designedEntry.

Lemma entry_intro_lithium_unfold `{!islaG Sigma} `{!threadG}
    (fact : Prop) (resource successor code : iProp Sigma) (pc : Z) :
  instr_body pc (⌜fact⌝ ∗ entrySource fact resource ∗ True) -∗
  successor -∗ code -∗ instr_body pc (designedEntry fact resource).
Proof.
  zesu_entry_intro_goal_if_enabled.
  lazymatch goal with
  | |- @bi_emp_valid _
      (instr_body pc (⌜fact⌝ ∗ entrySource fact resource ∗ True) -∗
       successor -∗ code -∗
       instr_body pc (⌜fact⌝ ∗ entrySource fact resource ∗ True))%I => idtac
  end.
  iStartProof. iIntros "Hbody _ _". iExact "Hbody".
Qed.
End Controls.
End RegisteredSource.

Module AbsentBinder.
Section Controls.
Context {Sigma : gFunctors}.
Definition entrySource (resource : iProp Sigma) : iProp Sigma := resource.
#[local] Instance : LithiumUnfold (@entrySource) := I.
Local Typeclasses Opaque entrySource.
#[local] Instance missing_binder_introduction resource (absent : nat) :
    ZesuEntryIntro (entrySource resource) (absent = absent).
Proof. unfold ZesuEntryIntro. iIntros "_". done. Qed.
Lemma entry_intro_absent_binder (resource peer : iProp Sigma) :
    entrySource resource ∗ peer ⊢ entrySource resource ∗ peer.
Proof.
  iIntros "[Hsource Hpeer]".
  let before := match goal with |- ?target => constr:(target) end in
  assert_fails zesu_entry_intro_if_enabled;
  let after := match goal with |- ?target => constr:(target) end in
  constr_eq before after. iFrame "Hsource Hpeer".
Qed.
End Controls.
End AbsentBinder.

Module DuplicateRegistration.
Section Controls.
Context {Sigma : gFunctors}.
Definition entrySource (left right : Prop) (resource : iProp Sigma) : iProp Sigma :=
  (⌜left /\ right⌝ ∗ resource)%I.
#[local] Instance : LithiumUnfold (@entrySource) := I.
Local Typeclasses Opaque entrySource.
#[local] Instance source_left left right resource :
    ZesuEntryIntro (entrySource left right resource) left.
Proof. unfold ZesuEntryIntro, entrySource. iIntros "[%Hfact _]". iPureIntro. tauto. Qed.
#[local] Instance source_right left right resource :
    ZesuEntryIntro (entrySource left right resource) right.
Proof. unfold ZesuEntryIntro, entrySource. iIntros "[%Hfact _]". iPureIntro. tauto. Qed.
Lemma entry_intro_duplicate_rejection (left right : Prop) (resource peer : iProp Sigma) :
    entrySource left right resource ∗ peer ⊢ entrySource left right resource ∗ peer.
Proof.
  iIntros "[Hsource Hpeer]".
  let original := match goal with |- ?target => constr:(target) end in
  pose (savedTarget := original).
  Fail zesu_entry_intro_if_enabled.
  let original := eval unfold savedTarget in savedTarget in
  let current := match goal with |- ?target => constr:(target) end in
  constr_eq original current. clear savedTarget. iFrame "Hsource Hpeer".
Qed.
End Controls.
End DuplicateRegistration.
