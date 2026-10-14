Require Import isla.riscv64.riscv64.

Class ZesuEntryIntro {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_entry_intro : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuEntryIntro + + - : typeclass_instances.

Class ZesuLoopStep {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_loop_step : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuLoopStep + + - : typeclass_instances.

Require Import ZesuSsz.Automation.SwitchDispatch.
From iris.proofmode Require Import intro_patterns.
From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Ltac2 @ external zesu_unique_entry_registration : unit -> unit :=
  "zesu-signature-gates.plugin" "unique_entry_registration".
Set Default Proof Mode "Classic".

Class ZesuStepEntryIntro : Prop := {}.

(* This proof-state marker is not a registered instance. *)
Inductive ZesuEntryIntroApplied {Sigma} (source : iProp Sigma)
    (facts : Prop) (evidence : ZesuEntryIntro source facts) : Prop :=
  ZesuEntryIntroWasApplied.

Lemma zesu_entry_intro_preserve {Sigma} (source : iProp Sigma) (facts : Prop)
    (intro : ZesuEntryIntro source facts) : source ⊢ ⌜facts⌝ ∗ source.
Proof.
  apply bi.persistent_entails_l;
    [typeclasses eauto | exact (@zesu_entry_intro Sigma source facts intro)].
Qed.

Ltac zesu_entry_intro_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEntryIntro);
  iMatchHyp ltac:(fun name source =>
    assert_fails (has_evar source);
      let evidence := open_constr:(ltac:(ltac2:(zesu_unique_entry_registration ()))
        : ZesuEntryIntro source _) in
      let evidenceType := type of evidence in
      assert_fails (has_evar evidence);
      assert_fails (has_evar evidenceType);
      lazymatch evidenceType with
      | @ZesuEntryIntro ?Sigma _ ?facts =>
          tryif match goal with
            | _ : @ZesuEntryIntroApplied Sigma source _ ?applied |- _ =>
                constr_eq evidence applied
            end
          then fail 0
          else
            tryif match goal with
              | _ : @ZesuEntryIntroApplied Sigma source _ _ |- _ => idtac
              end
            then fail 100 "The source has a different applied entry instance"
            else
          (tryif match goal with _ : facts |- _ => idtac end
          then idtac
          else
            let pattern := constr:(IList
              ((IPure IGallinaAnon :: IIdent name :: nil) :: nil)) in
            iDestruct (zesu_entry_intro_preserve source facts evidence with name)
              as pattern);
          let marker := fresh "HentryIntroApplied" in
          pose proof (@ZesuEntryIntroWasApplied Sigma source facts evidence) as marker
      end).
