Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import isla.riscv64.riscv64.

Module DualSourceCache.
Definition entry_fact (tag value : Z) : Prop := value = value.
Definition exit_fact (tag value : Z) : Prop := value = value.
Global Opaque entry_fact exit_fact.

Definition source {Sigma} (tag value : Z) (resource : iProp Sigma) : iProp Sigma :=
  (⌜entry_fact tag value /\ exit_fact tag value⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@source) := I.
Global Typeclasses Opaque source.
Definition wrapper {Sigma} (tag value : Z) (resource frame : iProp Sigma) : iProp Sigma :=
  (source tag value resource ∗ frame)%I.
Global Instance : LithiumUnfold (@wrapper) := I.
Global Typeclasses Opaque wrapper.

#[local] Instance exit_on : ZesuStepReturnRoute := I.
#[local] Instance entry_evidence {Sigma} (tag value : Z) (resource : iProp Sigma) :
    ZesuEntryIntro (source tag value resource) (entry_fact tag value).
Proof.
  rewrite /ZesuEntryIntro /source. iIntros "[%Hfacts _]".
  iPureIntro. exact (proj1 Hfacts).
Qed.
#[local] Instance exit_evidence {Sigma} (tag value : Z) (resource : iProp Sigma) :
    ZesuExitMeaning (source tag value resource) (exit_fact tag value).
Proof.
  rewrite /ZesuExitMeaning /source. iIntros "[%Hfacts _]".
  iPureIntro. exact (proj2 Hfacts).
Qed.

Lemma entry_exit_cache_integration `{!islaG Sigma} `{!threadG}
    (pc tag saved : Z) (resource frame : iProp Sigma) :
  instr_body pc
    (⌜entry_fact tag saved /\ exit_fact tag saved⌝ ∗ source tag saved resource ∗ frame) -∗
  instr_body pc (wrapper tag saved resource frame).
Proof.
  zesu_entry_intro_goal_if_enabled.
  lazymatch goal with
  | _ : @ZesuEntryIntroApplied Sigma (source tag saved resource) (entry_fact tag saved)
        (@entry_evidence Sigma tag saved resource) |- _ => idtac
  end.
  lazymatch goal with
  | _ : @ZesuExitMeaningApplied Sigma (source tag saved resource) (exit_fact tag saved)
        (@exit_evidence Sigma tag saved resource) |- _ => idtac
  end.
  zesu_cached_entry_fact_head constr:(entry_fact).
  Fail zesu_cached_entry_fact_head constr:(exit_fact).
  Fail zesu_entry_intro_goal_if_enabled.
  assert (Hentry_assignment : entry_fact tag saved ->
    (⊢ (∃ value : Z, ⌜entry_fact tag value⌝ : iProp Sigma))).
  { intro Hentry. iStartProof. zesu_conjunct_head_if_enabled.
    iPureIntro. exact Hentry. }
  assert (Hexit_refusal : exit_fact tag saved ->
    (⊢ (∃ value : Z, ⌜exit_fact tag value⌝ : iProp Sigma))).
  { intro Hexit. iStartProof. Fail zesu_conjunct_head_if_enabled.
    iExists saved. iPureIntro. exact Hexit. }
  change (⊢ instr_body pc
    (⌜entry_fact tag saved /\ exit_fact tag saved⌝ ∗ source tag saved resource ∗ frame) -∗
    instr_body pc
    (⌜entry_fact tag saved /\ exit_fact tag saved⌝ ∗ source tag saved resource ∗ frame))%I.
  iStartProof. iIntros "Hbody". iExact "Hbody".
Qed.
Print Assumptions entry_exit_cache_integration.
End DualSourceCache.
