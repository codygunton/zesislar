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

Lemma zesu_entry_intro_instr_body_equiv `{!islaG Sigma} `{!threadG}
    (pc : Z) (source frame : iProp Sigma) (facts : Prop)
    (intro : ZesuEntryIntro source facts) :
  instr_body pc (source ∗ frame) ⊣⊢
  instr_body pc (⌜facts⌝ ∗ source ∗ frame).
Proof.
  apply bi.equiv_entails_2; rewrite !instr_pre'_eq /instr_pre'_def /=.
  - iIntros "Hbody [%Hfacts [Hsource Hframe]]".
    iApply ("Hbody" with "[$Hsource $Hframe]").
  - iIntros "Hbody [Hsource Hframe]".
    iDestruct (zesu_entry_intro_preserve source facts intro with "Hsource")
      as "[%Hfacts Hsource]".
    iApply "Hbody". iFrame "Hsource Hframe". done.
Qed.

Lemma zesu_entry_intro_wand_equiv {PROP : bi} (premise before after : PROP) :
  before ⊣⊢ after -> (premise -∗ before) ⊣⊢ (premise -∗ after).
Proof. intros Hequivalent. by rewrite Hequivalent. Qed.

(* Inspect only the conclusion of the original wand prefix. *)
Ltac zesu_entry_intro_goal_term assertion continuation :=
  lazymatch assertion with
  | @bi_wand ?PROP ?premise ?tail =>
      zesu_entry_intro_goal_term tail
        ltac:(fun replacement equivalent Sigma source facts evidence =>
          let rewritten := constr:((premise -∗ replacement)%I) in
          let lifted := constr:(@zesu_entry_intro_wand_equiv PROP
            premise tail replacement equivalent) in
          continuation rewritten lifted Sigma source facts evidence)
  | @instr_pre' ?Arch ?Sigma ?isla ?thread false ?pc ?entry =>
      let head := get_head entry in
      let expanded := eval cbv beta delta [head] in entry in
      lazymatch expanded with
      | (?source ∗ ?frame)%I =>
          assert_fails (has_evar source);
          let evidence := open_constr:(ltac:(ltac2:(zesu_unique_entry_registration ()))
            : @ZesuEntryIntro Sigma source _) in
          let evidenceType := type of evidence in
          assert_fails (has_evar evidence);
          assert_fails (has_evar evidenceType);
          lazymatch evidenceType with
          | @ZesuEntryIntro Sigma _ ?facts =>
              tryif match goal with
                | _ : @ZesuEntryIntroApplied Sigma source _ _ |- _ => idtac
                end
              then fail 100 "The goal entry already has an applied instance"
              else
                let replacement := constr:(@instr_pre' Arch Sigma isla thread
                  false pc (⌜facts⌝ ∗ source ∗ frame)%I) in
                let equivalent := constr:(@zesu_entry_intro_instr_body_equiv
                  Sigma isla thread pc source frame facts evidence) in
                continuation replacement equivalent Sigma source facts evidence
          end
      end
  end.

Ltac zesu_entry_intro_goal_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEntryIntro);
  lazymatch goal with
  | |- @bi_emp_valid ?PROP ?assertion =>
      zesu_entry_intro_goal_term assertion
        ltac:(fun replacement equivalent Sigma source facts evidence =>
          rewrite equivalent;
          let marker := fresh "HentryIntroApplied" in
          pose proof (@ZesuEntryIntroWasApplied Sigma source facts evidence) as marker)
  end.

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
