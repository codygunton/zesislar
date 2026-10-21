Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.ExitMeaning.
Require Import isla.riscv64.riscv64.

(* The source remains intact when the second source-keyed class contributes facts. *)
Definition r3_exit_control_source {Sigma} (facts : Prop)
    (resource : iProp Sigma) : iProp Sigma := (⌜facts⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@r3_exit_control_source) := I.
Global Typeclasses Opaque r3_exit_control_source.
Definition r3_exit_control_wrapper {Sigma} (facts : Prop)
    (resource frame : iProp Sigma) : iProp Sigma :=
  (r3_exit_control_source facts resource ∗ frame)%I.
Global Instance : LithiumUnfold (@r3_exit_control_wrapper) := I.
Global Typeclasses Opaque r3_exit_control_wrapper.
#[local] Instance r3_exit_control_evidence {Sigma} (facts : Prop)
    (resource : iProp Sigma) :
  ZesuExitMeaning (r3_exit_control_source facts resource) facts.
Proof. rewrite /ZesuExitMeaning /r3_exit_control_source. iIntros "[%Hfacts _]". done. Qed.

Lemma r3_exit_goal_control `{!islaG Sigma} `{!threadG}
    (pc : Z) (facts : Prop) (premise resource frame : iProp Sigma) :
  (premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame)) -∗
  premise -∗ instr_body pc (r3_exit_control_wrapper facts resource frame).
Proof.
zesu_entry_intro_goal_if_enabled.
lazymatch goal with
| _ : @ZesuExitMeaningApplied Sigma (r3_exit_control_source facts resource) facts
      (@r3_exit_control_evidence Sigma facts resource) |- _ => idtac
end.
change (⊢ (premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame)) -∗
  premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame))%I.
iStartProof. iIntros "Hbody Hpremise". iApply ("Hbody" with "Hpremise").
Qed.
Print Assumptions r3_exit_goal_control.

(* Both source-keyed classes contribute once for a shared source. *)
#[local] Instance r3_dual_entry_on : ZesuStepEntryIntro := {}.
Definition r3_dual_source {Sigma} (left right : Prop)
    (resource : iProp Sigma) : iProp Sigma := (⌜left /\ right⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@r3_dual_source) := I.
Global Typeclasses Opaque r3_dual_source.
Definition r3_dual_wrapper {Sigma} (left right : Prop)
    (resource frame : iProp Sigma) : iProp Sigma :=
  (r3_dual_source left right resource ∗ frame)%I.
Global Instance : LithiumUnfold (@r3_dual_wrapper) := I.
Global Typeclasses Opaque r3_dual_wrapper.
#[local] Instance r3_dual_entry_evidence {Sigma} (left right : Prop)
    (resource : iProp Sigma) :
  ZesuEntryIntro (r3_dual_source left right resource) left.
Proof. rewrite /ZesuEntryIntro /r3_dual_source. iIntros "[%Hp _]". iPureIntro. tauto. Qed.
#[local] Instance r3_dual_exit_evidence {Sigma} (left right : Prop)
    (resource : iProp Sigma) :
  ZesuExitMeaning (r3_dual_source left right resource) right.
Proof. rewrite /ZesuExitMeaning /r3_dual_source. iIntros "[%Hp _]". iPureIntro. tauto. Qed.

Lemma r3_dual_source_control `{!islaG Sigma} `{!threadG}
    (pc : Z) (left right : Prop) (premise resource frame : iProp Sigma) :
  (premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame)) -∗
  premise -∗ instr_body pc (r3_dual_wrapper left right resource frame).
Proof.
zesu_entry_intro_goal_if_enabled.
lazymatch goal with
| _ : @ZesuEntryIntroApplied Sigma (r3_dual_source left right resource) left
      (@r3_dual_entry_evidence Sigma left right resource) |- _ => idtac
end.
lazymatch goal with
| _ : @ZesuExitMeaningApplied Sigma (r3_dual_source left right resource) right
      (@r3_dual_exit_evidence Sigma left right resource) |- _ => idtac
end.
Fail zesu_entry_intro_goal_if_enabled.
change (⊢ (premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame)) -∗
  premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame))%I.
iStartProof. iIntros "Hbody Hpremise". iApply ("Hbody" with "Hpremise").
Qed.
Print Assumptions r3_dual_source_control.
