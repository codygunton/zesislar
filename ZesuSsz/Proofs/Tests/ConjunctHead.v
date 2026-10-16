Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
From iris.proofmode Require Import environments.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Definition r1c_tagged (value : Z) : Prop := value = value.
Definition r1c_other (value : Z) : Prop := value = value.
#[local] Hint Extern 1 (SimplAnd (?flag = true) True) =>
  match goal with
  | Hguard : flag = true |- _ =>
      unfold SimplAnd; split; [intros _; exact Hguard | intros _; exact I]
  end : typeclass_instances.

#[local] Hint Extern 1 (SimplAnd (r1c_tagged ?value) True) =>
  unfold SimplAnd; split;
  [intros _; first [assumption | match goal with
    Hguard : ?flag = true, Hfact : ?flag = true -> r1c_tagged value |- _ =>
      exact (Hfact Hguard)
    end] | intros _; exact I] : typeclass_instances.

Global Opaque r1c_tagged r1c_other.

Definition r1c_seed_source {Sigma : gFunctors} (facts : Prop) : iProp Sigma := ⌜facts⌝%I.
#[local] Instance : LithiumUnfold (@r1c_seed_source) := I.
Local Typeclasses Opaque r1c_seed_source.
#[local] Instance r1c_seed_evidence {Sigma : gFunctors} facts :
  ZesuEntryIntro (@r1c_seed_source Sigma facts) facts.
Proof. rewrite /ZesuEntryIntro /r1c_seed_source. done. Qed.
Ltac r1c_record_head_scope Sigma facts :=
  let name := fresh "HentryApplied" in
  pose proof (@ZesuEntryIntroWasApplied Sigma (r1c_seed_source facts) facts
    (@r1c_seed_evidence Sigma facts)) as name;
  zesu_cache_entry_intro_heads facts.
Ltac r1c_collect_head_scope :=
  lazymatch goal with _ : @ZesuEntryIntroApplied _ _ ?facts _ |- _ =>
    zesu_cache_entry_intro_heads facts
  end.
Ltac r1c_require_permitted_head head :=
  let inspect := ltac2:(head |-
    let head := Option.get (Ltac1.to_constr head) in
    if zesu_permitted_fact_head head then ()
    else Control.zero (Tactic_failure None)) in
  inspect head.

Lemma r1c_constant_assignment (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_constant_assignment.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_ambiguous (Sigma : gFunctors) (Hleft : r1c_tagged 1) (Hright : r1c_tagged 2) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 1. iPureIntro. exact Hleft.
Qed.
Print Assumptions r1c_ambiguous.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_absent_head (Sigma : gFunctors) (Hother : r1c_other 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent r1c_tagged.
iExists 0. iPureIntro. unfold r1c_tagged. reflexivity.
Qed.
Print Assumptions r1c_absent_head.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_ignored_binder (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (∃ value : Z, True : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 0. done.
Qed.
Print Assumptions r1c_ignored_binder.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_variable_head (Sigma : gFunctors) (Fact : Z -> Prop) (Hfact : Fact 42) :
    ⊢ (∃ value : Z, ⌜Fact value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 42. iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_variable_head.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_unregistered_premise (Sigma : gFunctors) (Premise : Prop) (Hpremise : Premise) (Hfact : Premise -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 42. iPureIntro. exact (Hfact Hpremise).
Qed.
Print Assumptions r1c_unregistered_premise.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_registered_guard (Sigma : gFunctors) (flag : bool) (Hguard : flag = true) (Hfact : flag = true -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact (Hfact Hguard).
Qed.
Print Assumptions r1c_registered_guard.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_absent_guard (Sigma : gFunctors) (flag : bool) (Hfact : flag = true -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent r1c_tagged.
iExists 0. iPureIntro. unfold r1c_tagged. reflexivity.
Qed.
Print Assumptions r1c_absent_guard.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_reordered (Sigma : gFunctors) (Hfact : r1c_tagged 42) (Hother : r1c_other 7) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_reordered.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_plain_goal (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (True : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
done.
Qed.
Print Assumptions r1c_plain_goal.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_ambiguous (Sigma : gFunctors) (inputPrefix : bv 64) (headerSaved otherSaved : Z) (Hheader : headerSaved = (1 + (bv_unsigned inputPrefix - 183))%Z) (Hother : otherSaved = (1 + (bv_unsigned inputPrefix - 183))%Z) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + (bv_unsigned inputPrefix - 183))%Z⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists headerSaved. iPureIntro. exact Hheader.
Qed.
Print Assumptions r1c_real_eq_ambiguous.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_header_discrimination (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + n)%Z⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists headerSaved. iPureIntro. exact Hheader.
Qed.
Print Assumptions r1c_real_eq_header_discrimination.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_payload_discrimination (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) :
    ⊢ (∃ payloadLength : Z, ⌜payloadLength = bigEndian lengthBytes⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists payloadSaved. iPureIntro. exact Hpayload.
Qed.
Print Assumptions r1c_real_eq_payload_discrimination.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_fixed_mismatch (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) (inputPrefix : bv 64) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + (bv_unsigned inputPrefix - 183))%Z⌝ : iProp Sigma).
Proof.
r1c_record_head_scope Sigma constr:(forall value : Z, r1c_tagged value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists (1 + (bv_unsigned inputPrefix - 183))%Z. iPureIntro. reflexivity.
Qed.
Print Assumptions r1c_real_eq_fixed_mismatch.

(* Registered-head scope controls. Logical heads remain excluded. *)
Module RegisteredHeadControls.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Open Scope Z_scope.
Definition scoped_fact (tag value : Z) : Prop := value = value.
Definition unregistered_fact (tag value : Z) : Prop := value = value.
Definition entry_fact (tag value : Z) : Prop := value = value.
Definition opaque_container (fact : Prop) : Prop := True.
Global Opaque scoped_fact unregistered_fact entry_fact opaque_container.
#[local] Hint Extern 1 (SimplAnd (scoped_fact ?tag ?value) True) =>
  match goal with Hknown : scoped_fact tag value |- _ =>
    unfold SimplAnd; split; [intros _; exact Hknown | intros _; exact I]
  end : typeclass_instances.
Definition entry_scope_source {Sigma} (tag : Z) : iProp Sigma :=
  (⌜exists value : Z, entry_fact tag value⌝)%I.
#[local] Instance : LithiumUnfold (@entry_scope_source) := I.
Local Typeclasses Opaque entry_scope_source.
#[local] Instance entry_scope_evidence {Sigma : gFunctors} (tag : Z) :
  ZesuEntryIntro (@entry_scope_source Sigma tag) (exists value : Z, entry_fact tag value).
Proof. rewrite /ZesuEntryIntro /entry_scope_source. done. Qed.
Definition container_scope_source {Sigma} (tag saved : Z) : iProp Sigma :=
  (⌜opaque_container (entry_fact tag saved)⌝)%I.
#[local] Instance : LithiumUnfold (@container_scope_source) := I.
Local Typeclasses Opaque container_scope_source.
#[local] Instance container_scope_evidence {Sigma : gFunctors} (tag saved : Z) :
  ZesuEntryIntro (@container_scope_source Sigma tag saved) (opaque_container (entry_fact tag saved)).
Proof. rewrite /ZesuEntryIntro /container_scope_source. done. Qed.

Lemma r1c_registered_semantic (Sigma : gFunctors) (tag saved : Z) (Hfact : scoped_fact tag saved) : (⊢ (∃ value : Z, ⌜scoped_fact tag value⌝ : iProp Sigma)).
Proof.
r1c_record_head_scope Sigma constr:(forall tag value : Z, scoped_fact tag value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_registered_semantic.

Lemma r1c_entry_semantic (Sigma : gFunctors) (tag saved : Z) (Hfact : entry_fact tag saved) : (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma)).
Proof.
pose proof (@ZesuEntryIntroWasApplied Sigma (entry_scope_source tag) (exists value : Z, entry_fact tag value) (@entry_scope_evidence Sigma tag)) as Happlied. r1c_collect_head_scope. iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_entry_semantic.

Lemma r1c_unregistered_semantic (Sigma : gFunctors) (tag saved : Z) (Hfact : unregistered_fact tag saved) : (⊢ (∃ value : Z, ⌜unregistered_fact tag value⌝ : iProp Sigma)).
Proof.
r1c_record_head_scope Sigma constr:(forall tag value : Z, scoped_fact tag value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_unregistered_semantic.

Lemma r1c_ambiguous_semantic (Sigma : gFunctors) (tag : Z) (Hleft : scoped_fact tag 7) (Hright : scoped_fact tag 9) : (⊢ (∃ value : Z, ⌜scoped_fact tag value⌝ : iProp Sigma)).
Proof.
r1c_record_head_scope Sigma constr:(forall tag value : Z, scoped_fact tag value).
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 7. iPureIntro. exact Hleft.
Qed.
Print Assumptions r1c_ambiguous_semantic.

Lemma r1c_opaque_argument (Sigma : gFunctors) (tag saved : Z) (Hfact : entry_fact tag saved) : (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma)).
Proof.
pose proof (@ZesuEntryIntroWasApplied Sigma (container_scope_source tag saved) (opaque_container (entry_fact tag saved)) (@container_scope_evidence Sigma tag saved)) as Happlied. r1c_collect_head_scope. iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_opaque_argument.

Lemma r1c_arithmetic_lt (Sigma : gFunctors) (saved bound : Z) (Hguard : saved < bound) : (⊢ (∃ value : Z, ⌜value < bound⌝ : iProp Sigma)).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hguard.
Qed.
Print Assumptions r1c_arithmetic_lt.

Lemma r1c_arithmetic_le (Sigma : gFunctors) (saved bound : Z) (Hguard : saved <= bound) : (⊢ (∃ value : Z, ⌜value <= bound⌝ : iProp Sigma)).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hguard.
Qed.
Print Assumptions r1c_arithmetic_le.

Lemma r1c_arithmetic_eq (Sigma : gFunctors) (saved bound : Z) (Hguard : saved = bound) : (⊢ (∃ value : Z, ⌜value = bound⌝ : iProp Sigma)).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hguard.
Qed.
Print Assumptions r1c_arithmetic_eq.

Lemma r1c_excluded_lt  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(Z.lt).
exact I.
Qed.
Print Assumptions r1c_excluded_lt.

Lemma r1c_excluded_le  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(Z.le).
exact I.
Qed.
Print Assumptions r1c_excluded_le.

Lemma r1c_excluded_eq  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(@eq).
exact I.
Qed.
Print Assumptions r1c_excluded_eq.

Lemma r1c_excluded_and  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(and).
exact I.
Qed.
Print Assumptions r1c_excluded_and.

Lemma r1c_excluded_or  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(or).
exact I.
Qed.
Print Assumptions r1c_excluded_or.

Lemma r1c_excluded_iff  : True.
Proof.
idtac.
Fail r1c_require_permitted_head constr:(iff).
exact I.
Qed.
Print Assumptions r1c_excluded_iff.

Lemma r1c_guard_before_semantic (Sigma : gFunctors) (tag saved index inputLength : Z) (Hfact : scoped_fact tag saved) (Hnative : saved < inputLength) (Hcorrect : index < saved) : (⊢ (∃ width value : Z, ⌜value < width /\ scoped_fact tag width⌝ : iProp Sigma)).
Proof.
r1c_record_head_scope Sigma constr:(forall tag value : Z, scoped_fact tag value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. split; [exact Hcorrect | exact Hfact].
Qed.
Print Assumptions r1c_guard_before_semantic.

Lemma r1c_reordered_semantic (Sigma : gFunctors) (tag saved : Z) (Hfact : scoped_fact tag saved) (Hother : unregistered_fact tag 17) : (⊢ (∃ value : Z, ⌜scoped_fact tag value⌝ : iProp Sigma)).
Proof.
r1c_record_head_scope Sigma constr:(forall tag value : Z, scoped_fact tag value).
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_reordered_semantic.
#[local] Hint Extern 1 (SimplAnd (?flag = true) True) =>
  match goal with Hguard : flag = true |- _ =>
    unfold SimplAnd; split; [intros _; exact Hguard | intros _; exact I]
  end : typeclass_instances.

Lemma r1c_registered_guard (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hguard : flag = true) (Hfact : flag = true -> entry_fact tag saved) : (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma)).
Proof.
pose proof (@ZesuEntryIntroWasApplied Sigma (entry_scope_source tag) (exists value : Z, entry_fact tag value) (@entry_scope_evidence Sigma tag)) as Happlied. r1c_collect_head_scope. iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact (Hfact Hguard).
Qed.
Print Assumptions r1c_registered_guard.

Lemma r1c_unregistered_premise (Sigma : gFunctors) (tag saved : Z) (Premise : Prop) (Hpremise : Premise) (Hfact : Premise -> entry_fact tag saved) : (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma)).
Proof.
pose proof (@ZesuEntryIntroWasApplied Sigma (entry_scope_source tag) (exists value : Z, entry_fact tag value) (@entry_scope_evidence Sigma tag)) as Happlied. r1c_collect_head_scope. iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact (Hfact Hpremise).
Qed.
Print Assumptions r1c_unregistered_premise.

Lemma r1c_absent_guard (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hfact : flag = true -> entry_fact tag saved) : (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma)).
Proof.
pose proof (@ZesuEntryIntroWasApplied Sigma (entry_scope_source tag) (exists value : Z, entry_fact tag value) (@entry_scope_evidence Sigma tag)) as Happlied. r1c_collect_head_scope. iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent entry_fact. iExists 0. iPureIntro. unfold entry_fact. reflexivity.
Qed.
Print Assumptions r1c_absent_guard.

End RegisteredHeadControls.

Module CachedHeadControls.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Require Import ZesuSsz.Automation.Switches.EntryIntro.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Definition cached_fact (tag value : Z) : Prop := value = value.
Definition other_fact (tag value : Z) : Prop := value = value.
Global Opaque cached_fact other_fact.
Definition cache_source {Sigma : gFunctors} (facts : Prop) : iProp Sigma := ⌜facts⌝%I.
#[local] Instance : LithiumUnfold (@cache_source) := I.
Local Typeclasses Opaque cache_source.
#[local] Instance cache_evidence {Sigma : gFunctors} (facts : Prop) :
  ZesuEntryIntro (@cache_source Sigma facts) facts.
Proof. rewrite /ZesuEntryIntro /cache_source. done. Qed.
Ltac record_heads Sigma facts :=
  let name := fresh "HentryApplied" in
  pose proof (@ZesuEntryIntroWasApplied Sigma (cache_source facts) facts
    (@cache_evidence Sigma facts)) as name;
  zesu_cache_entry_intro_heads facts.
#[local] Hint Extern 1 (SimplAnd (other_fact ?tag ?value) True) =>
  match goal with Hknown : other_fact tag value |- _ =>
    unfold SimplAnd; split; [intros _; exact Hknown | intros _; exact I]
  end : typeclass_instances.
#[local] Hint Extern 1 (SimplAnd (?flag = true) True) =>
  match goal with Hguard : flag = true |- _ =>
    unfold SimplAnd; split; [intros _; exact Hguard | intros _; exact I]
  end : typeclass_instances.
Definition body_source {Sigma : gFunctors} (tag saved : Z) (resource : iProp Sigma) : iProp Sigma := (⌜cached_fact tag saved⌝ ∗ resource)%I.
#[local] Instance : LithiumUnfold (@body_source) := I.
Local Typeclasses Opaque body_source.
#[local] Instance body_evidence {Sigma : gFunctors} tag saved resource :
  ZesuEntryIntro (@body_source Sigma tag saved resource) (cached_fact tag saved).
Proof. rewrite /ZesuEntryIntro /body_source. iIntros "[%Hfact _]". done. Qed.
Definition body_wrapper {Sigma : gFunctors} tag saved (resource frame : iProp Sigma) : iProp Sigma := (body_source tag saved resource ∗ frame)%I.
#[local] Instance : LithiumUnfold (@body_wrapper) := I.
Local Typeclasses Opaque body_wrapper.
Definition fits_guard (flag : bool) : Prop := flag = true.
Lemma fits_guard_from_bool flag : flag = true -> fits_guard flag.
Proof. unfold fits_guard. auto. Qed.
Global Opaque fits_guard.
#[local] Hint Extern 1 (SimplAnd (fits_guard ?flag) True) =>
  match goal with Hguard : flag = true |- _ =>
    unfold SimplAnd; split;
      [intros _; exact (fits_guard_from_bool flag Hguard) | intros _; exact I]
  end : typeclass_instances.
From Ltac2 Require Import Ltac2.
Ltac2 count_bridge (solver : Ltac1.t) (operation : Ltac1.t) :=
  let calls := { contents := 0 } in
  let counted := Ltac1.lambda (fun premise =>
    calls.(contents) := Int.add (calls.(contents)) 1;
    let result := { contents := None } in
    Ltac1.apply solver [premise] (fun proof => result.(contents) := Some proof);
    Option.get (result.(contents))) in
  Ltac1.apply operation [counted] Ltac1.run;
  if Int.equal (calls.(contents)) 1 then ()
  else Control.zero (Tactic_failure (Some (Message.of_string "The bridge call count differs from one."))).
Set Default Proof Mode "Classic".
Ltac counted_match :=
  let bridge := ltac2:(solver operation |- count_bridge solver operation) in
  bridge ltac:(fun premise => zesu_registered_pure_fact premise)
    ltac:(fun solver => zesu_witness_open_existentials constr:(12%nat);
      lazymatch goal with |- envs_entails _ ?requested =>
        progress (zesu_match_resource_pure_heads solver constr:(4%nat) requested)
      end).

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_matching : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_matching.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_no_marker : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_no_marker.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_cache_without_applied : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. zesu_cache_entry_intro_heads constr:(exists value : Z, cached_fact tag value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_cache_without_applied.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_applied_without_cache : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. pose proof (@ZesuEntryIntroWasApplied Sigma (cache_source (cached_fact tag saved)) (cached_fact tag saved) (@cache_evidence Sigma (cached_fact tag saved))) as Happlied. iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_applied_without_cache.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_unlisted_registered_head : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : other_fact tag saved), (⊢ (∃ value : Z, ⌜other_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_unlisted_registered_head.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_ambiguous : forall (Sigma : gFunctors) (tag : Z) (Hleft : cached_fact tag 1) (Hright : cached_fact tag 2), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag Hleft Hright. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 1. iPureIntro. exact Hleft.
Qed.
Print Assumptions head_cache_ambiguous.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_reordered : forall (Sigma : gFunctors) (tag saved : Z) (Hother : other_fact tag 17) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hother Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_reordered.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_no_qualification_query : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_witness_open_existentials constr:(12%nat); lazymatch goal with |- envs_entails _ ?requested => progress (zesu_match_resource_pure_heads ltac:(fun _ => fail 100 "The qualification solver executed.") constr:(4%nat) requested) end.
iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_no_qualification_query.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_variable_head : forall (Sigma : gFunctors) (Fact : Z -> Prop) (Hfact : Fact 42), (⊢ (∃ value : Z, ⌜Fact value⌝ : iProp Sigma)).
Proof.
intros Sigma Fact Hfact. record_heads Sigma constr:(forall value : Z, Fact value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 42. iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_variable_head.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_lt : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(Z.lt).
exact I.
Qed.
Print Assumptions head_cache_excluded_lt.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_le : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(Z.le).
exact I.
Qed.
Print Assumptions head_cache_excluded_le.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_eq : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(@eq).
exact I.
Qed.
Print Assumptions head_cache_excluded_eq.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_and : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(and).
exact I.
Qed.
Print Assumptions head_cache_excluded_and.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_or : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(or).
exact I.
Qed.
Print Assumptions head_cache_excluded_or.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_excluded_iff : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ (0 < 1 /\ 0 <= 1 /\ 0 = 0 /\ (True \/ False) /\ (True <-> True))).
Fail zesu_cached_entry_fact_head constr:(iff).
exact I.
Qed.
Print Assumptions head_cache_excluded_iff.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_deduplicated : forall (Sigma : gFunctors) (tag saved : Z), True.
Proof.
intros Sigma tag saved. record_heads Sigma constr:(cached_fact tag saved /\ cached_fact tag 17).
zesu_cache_entry_intro_heads constr:(cached_fact tag saved /\ cached_fact tag 17).
lazymatch goal with _ : ZesuEntryIntroHeads ((@ZesuEntryIntroHead _ cached_fact) /\ True) |- _ => idtac end. exact I.
Qed.
Print Assumptions head_cache_deduplicated.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_guard_before_semantic : forall (Sigma : gFunctors) (tag saved index inputLength : Z) (Hfact : cached_fact tag saved) (Hnative : saved < inputLength) (Hcorrect : index < saved), (⊢ (∃ width value : Z, ⌜value < width /\ cached_fact tag width⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved index inputLength Hfact Hnative Hcorrect. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. split; [exact Hcorrect | exact Hfact].
Qed.
Print Assumptions head_cache_guard_before_semantic.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_closed_guard : forall (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hguard : flag = true) (Hfact : flag = true -> cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved flag Hguard Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact (Hfact Hguard).
Qed.
Print Assumptions head_cache_closed_guard.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_absent_guard : forall (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hfact : flag = true -> cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved flag Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent cached_fact. iExists 0. iPureIntro. unfold cached_fact. reflexivity.
Qed.
Print Assumptions head_cache_absent_guard.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_goal_introduction : forall (Sigma : gFunctors) (isla : islaG Sigma) (thread : threadG) (pc tag saved : Z) (resource frame : iProp Sigma), (⊢ instr_body pc (⌜cached_fact tag saved⌝ ∗ body_source tag saved resource ∗ frame) -∗ instr_body pc (body_wrapper tag saved resource frame)).
Proof.
intros Sigma isla thread pc tag saved resource frame.
zesu_entry_intro_goal_if_enabled.
zesu_cached_entry_fact_head constr:(cached_fact). Fail zesu_entry_intro_goal_if_enabled. iStartProof. iIntros "Hbody". iExact "Hbody".
Qed.
Print Assumptions head_cache_goal_introduction.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_peer_shelf : forall (Sigma : gFunctors) (tag saved : Z) (Hfact : cached_fact tag saved), ((⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)) /\ True).
Proof.
intros Sigma tag saved Hfact. assert (Hpending : True) by shelve. split. 1: record_heads Sigma constr:(exists value : Z, cached_fact tag value). 1: iStartProof.
1: zesu_conjunct_head_if_enabled.
1: iPureIntro; exact Hfact. 1: exact I. Unshelve. all: exact I.
Qed.
Print Assumptions head_cache_peer_shelf.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_registered_bridge_once : forall (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hguard : flag = true) (Hfact : fits_guard flag -> cached_fact tag saved), (⊢ (∃ left right : Z, ⌜cached_fact tag left /\ cached_fact tag right⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved flag Hguard Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
counted_match.
match goal with _ : @ZesuConjunctPremiseApplied (fits_guard flag) ?proof |- _ => assert_fails (has_evar proof) end. iPureIntro. split; exact (Hfact (fits_guard_from_bool flag Hguard)).
Qed.
Print Assumptions head_cache_registered_bridge_once.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_unrelated_implication_no_query : forall (Sigma : gFunctors) (tag saved : Z) (flag : bool) (Hfact : cached_fact tag saved) (Hunrelated : fits_guard flag -> other_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved flag Hfact Hunrelated. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
zesu_witness_open_existentials constr:(12%nat); lazymatch goal with |- envs_entails _ ?requested => progress (zesu_match_resource_pure_heads ltac:(fun _ => fail 100 "An unrelated implication invoked its solver.") constr:(4%nat) requested) end.
iPureIntro. exact Hfact.
Qed.
Print Assumptions head_cache_unrelated_implication_no_query.

Global Opaque cached_fact other_fact fits_guard.
Lemma head_cache_unregistered_premise : forall (Sigma : gFunctors) (tag saved : Z) (Premise : Prop) (Hpremise : Premise) (Hfact : Premise -> cached_fact tag saved), (⊢ (∃ value : Z, ⌜cached_fact tag value⌝ : iProp Sigma)).
Proof.
intros Sigma tag saved Premise Hpremise Hfact. record_heads Sigma constr:(exists value : Z, cached_fact tag value). iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists saved. iPureIntro. exact (Hfact Hpremise).
Qed.
Print Assumptions head_cache_unregistered_premise.

End CachedHeadControls.
