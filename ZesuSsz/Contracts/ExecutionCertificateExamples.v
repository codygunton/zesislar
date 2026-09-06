From Coq Require Import Lia ZArith.ZArith.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.

Open Scope Z_scope.

Definition examplePc (state : nat) : option Z :=
  match state with 0%nat => Some 0 | 1%nat => Some 1 | _ => Some 2 end.
Definition exampleEntry (_ : unit) (state : nat) : Prop := state = 0%nat.
Definition exampleRegion (address : Z) : Prop := address = 0.
Definition exampleExit (address : Z) : Prop := address = 1.

Definition exitOrSelfLoopStep (_ : nat) (before after : nat) : Prop :=
  before = 0%nat /\ (after = 0%nat \/ after = 1%nat).

Lemma exitOrSelfLoopRejected :
  ~ ExecutionPathCertificate exitOrSelfLoopStep examplePc exampleEntry
      exampleRegion exampleExit 0 (fun _ => 1%nat).
Proof.
  intros Hcertificate.
  eapply (executionNoInfinite _ _ _ _ _ _ _ Hcertificate tt 0%nat 0%nat).
  - reflexivity.
  - exists (fun _ => 0%nat). split; [reflexivity |].
    intros offset. split.
    + intros address Hpc Hexit. cbn in Hpc. inversion Hpc. subst. unfold exampleExit in Hexit. lia.
    + split; auto.
Qed.

Definition exitOrEscapeStep (_ : nat) (before after : nat) : Prop :=
  before = 0%nat /\ (after = 1%nat \/ after = 2%nat).

Lemma exitOrEscapeRejected :
  ~ ExecutionPathCertificate exitOrEscapeStep examplePc exampleEntry
      exampleRegion exampleExit 0 (fun _ => 1%nat).
Proof.
  intros Hcertificate.
  pose proof (executionPrefixes _ _ _ _ _ _ _ Hcertificate
    tt 0%nat 1%nat 0%nat 2%nat eq_refl) as Hprefix.
  assert (Htrace :
    StoppedTrace exitOrEscapeStep examplePc exampleExit 0%nat 1%nat 0%nat 2%nat).
  { econstructor.
    - intros address Hpc Hexit. cbn in Hpc. inversion Hpc. subst. unfold exampleExit in Hexit. lia.
    - split; auto.
    - constructor. }
  specialize (Hprefix Htrace).
  destruct Hprefix as (_ & address & Hpc & [Hregion | Hexit]).
  - cbn in Hpc. inversion Hpc. subst.
    unfold exampleRegion in Hregion. lia.
  - cbn in Hpc. inversion Hpc. subst.
    unfold exampleExit in Hexit. lia.
Qed.

Definition deadEndStep (_ : nat) (_ _ : nat) : Prop := False.

Lemma deadEndRejected :
  ~ ExecutionPathCertificate deadEndStep examplePc exampleEntry
      exampleRegion exampleExit 0 (fun _ => 1%nat).
Proof.
  intros Hcertificate.
  destruct (executionProgress _ _ _ _ _ _ _ Hcertificate
    tt 0%nat 0%nat 0%nat 0%nat eq_refl (StoppedTraceRefl _ _ _ 0%nat 0%nat)) as (next & Hstep).
  - intros address Hpc Hexit. cbn in Hpc. inversion Hpc. subst. unfold exampleExit in Hexit. lia.
  - exact Hstep.
Qed.

Definition exitThenCallerLoopStep (_ : nat) (before after : nat) : Prop :=
  (before = 0%nat /\ after = 1%nat) \/
  (before = 1%nat /\ after = 1%nat).

Definition exitThenCallerInvariant (_ : unit) (state : nat) : Prop :=
  state = 0%nat \/ state = 1%nat.
Definition exitThenCallerRank (_ : unit) (state : nat) : nat :=
  match state with 0%nat => 1%nat | _ => 0%nat end.

Lemma exitThenCallerObligations :
  DecreasingExecutionObligations exitThenCallerLoopStep examplePc exampleEntry
    exampleRegion exampleExit 0 (fun _ => 1%nat).
Proof.
  refine {| executionInvariant := exitThenCallerInvariant;
            executionRank := exitThenCallerRank |}.
  - intros [] state ->. reflexivity.
  - unfold exampleExit. lia.
  - intros [] state ->. left. reflexivity.
  - intros [] state [-> | ->]; eexists; reflexivity.
  - intros [] state address [-> | ->] Hpc; cbn in Hpc; inversion Hpc; subst.
    + left. split; unfold exampleRegion, exampleExit; lia.
    + right. unfold exampleExit. reflexivity.
  - intros [] index state [-> | ->] HnotExit.
    + exists 1%nat. left. auto.
    + exfalso. eapply (HnotExit 1); [reflexivity | unfold exampleExit; reflexivity].
  - intros [] index before after [-> | ->] HnotExit Hstep.
    + destruct Hstep as [[_ ->] | [Hfalse _]]; [right; reflexivity | lia].
    + exfalso. eapply (HnotExit 1); [reflexivity | unfold exampleExit; reflexivity].
  - intros [] index before after [-> | ->] HnotExit Hstep.
    + destruct Hstep as [[_ ->] | [Hfalse _]]; [cbn; lia | lia].
    + exfalso. eapply (HnotExit 1); [reflexivity | unfold exampleExit; reflexivity].
  - intros [] state ->. cbn. lia.
Qed.

Lemma exitThenCallerLoopAccepted :
  ExecutionPathCertificate exitThenCallerLoopStep examplePc exampleEntry
    exampleRegion exampleExit 0 (fun _ => 1%nat).
Proof.
  apply executionCertificateFromDecrease.
  exact exitThenCallerObligations.
Qed.

Print Assumptions exitOrSelfLoopRejected.
Print Assumptions exitOrEscapeRejected.
Print Assumptions deadEndRejected.
Print Assumptions exitThenCallerLoopAccepted.
