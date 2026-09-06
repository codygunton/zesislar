From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.Machine.

Record DecreasingExecutionObligations {State Args : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (entry : Args -> State -> Prop)
    (region exitPc : Z -> Prop) (entryPc : Z)
    (bound : Args -> nat) : Type := {
  executionInvariant : Args -> State -> Prop;
  executionRank : Args -> State -> nat;
  obligationEntryPc :
    forall args state, entry args state -> pc state = Some entryPc;
  obligationEntryNotExit : ~ exitPc entryPc;
  obligationEntryInvariant :
    forall args state, entry args state -> executionInvariant args state;
  obligationPcDefined :
    forall args state,
      executionInvariant args state ->
      exists address, pc state = Some address;
  obligationPcClassified :
    forall args state address,
      executionInvariant args state ->
      pc state = Some address ->
      (region address /\ ~ exitPc address) \/ exitPc address;
  obligationProgress :
    forall args index state,
      executionInvariant args state ->
      (forall address, pc state = Some address -> ~ exitPc address) ->
      exists next, step index state next;
  obligationPreservation :
    forall args index before after,
      executionInvariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after ->
      executionInvariant args after;
  obligationDecrease :
    forall args index before after,
      executionInvariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after ->
      (executionRank args after < executionRank args before)%nat;
  obligationEntryBound :
    forall args state,
      entry args state -> (executionRank args state <= bound args)%nat
}.

Lemma stoppedTraceInvariant {State Args}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (exitPc : Z -> Prop)
    (invariant : Args -> State -> Prop)
    (preserved : forall args index before after,
      invariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after -> invariant args after) :
  forall args fromStep count before after,
    invariant args before ->
    StoppedTrace step pc exitPc fromStep count before after ->
    invariant args after.
Proof.
  intros args fromStep count before after Hinvariant Htrace.
  induction Htrace.
  - exact Hinvariant.
  - apply IHHtrace.
    eapply preserved; eassumption.
Qed.

Lemma stoppedTraceRankBound {State Args}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (exitPc : Z -> Prop)
    (invariant : Args -> State -> Prop) (rank : Args -> State -> nat)
    (preserved : forall args index before after,
      invariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after -> invariant args after)
    (decreases : forall args index before after,
      invariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after -> (rank args after < rank args before)%nat) :
  forall args fromStep count before after,
    invariant args before ->
    StoppedTrace step pc exitPc fromStep count before after ->
    (count <= rank args before)%nat.
Proof.
  intros args fromStep count before after Hinvariant Htrace.
  induction Htrace.
  - simpl. lia.
  - pose proof (preserved args fromStep before middle
      Hinvariant H H0) as Hmiddle.
    pose proof (decreases args fromStep before middle
      Hinvariant H H0) as Hdecrease.
    specialize (IHHtrace Hmiddle). simpl. lia.
Qed.

Lemma infiniteStoppedPrefix {State}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (exitPc : Z -> Prop)
    (run : nat -> State) (fromStep count : nat)
    (Hrun : forall offset,
      (forall address, pc (run offset) = Some address -> ~ exitPc address) /\
      step (fromStep + offset)%nat (run offset) (run (S offset))) :
  StoppedTrace step pc exitPc fromStep count (run 0) (run count).
Proof.
  revert fromStep run Hrun.
  induction count as [|count IH]; intros fromStep run Hrun.
  - constructor.
  - econstructor.
    + exact (proj1 (Hrun 0)).
    + replace fromStep with (fromStep + 0)%nat by lia.
      exact (proj2 (Hrun 0)).
    + change (StoppedTrace step pc exitPc (S fromStep) count
        ((fun n => run (S n)) 0) ((fun n => run (S n)) count)).
      apply (IH (S fromStep) (fun n => run (S n))).
      intros offset. specialize (Hrun (S offset)).
      replace (S fromStep + offset)%nat with
        (fromStep + S offset)%nat by lia.
      exact Hrun.
Qed.

Lemma stoppedTerminationFromDecrease {State Args}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (region exitPc : Z -> Prop)
    (invariant : Args -> State -> Prop) (rank : Args -> State -> nat)
    (defined : forall args state,
      invariant args state -> exists address, pc state = Some address)
    (classified : forall args state address,
      invariant args state -> pc state = Some address ->
      (region address /\ ~ exitPc address) \/ exitPc address)
    (progress : forall args index state,
      invariant args state ->
      (forall address, pc state = Some address -> ~ exitPc address) ->
      exists next, step index state next)
    (preserved : forall args index before after,
      invariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after -> invariant args after)
    (decreases : forall args index before after,
      invariant args before ->
      (forall address, pc before = Some address -> ~ exitPc address) ->
      step index before after -> (rank args after < rank args before)%nat) :
  forall args fromStep before,
    invariant args before ->
    exists count after,
      (count <= rank args before)%nat /\
      StoppedTrace step pc exitPc fromStep count before after /\
      exists address, pc after = Some address /\ exitPc address.
Proof.
  intros args fromStep before Hinvariant.
  remember (rank args before) as budget eqn:Hbudget.
  revert args fromStep before Hinvariant Hbudget.
  induction budget using lt_wf_ind.
  intros args fromStep before Hinvariant Hbudget.
  destruct (defined args before Hinvariant) as (address & Hpc).
  destruct (classified args before address Hinvariant Hpc)
    as [[Hregion HnotAddressExit] | Hexit].
  - assert (HnotExit : forall terminal,
        pc before = Some terminal -> ~ exitPc terminal).
    { intros terminal Hterminal. rewrite Hpc in Hterminal.
      inversion Hterminal. subst. exact HnotAddressExit. }
    destruct (progress args fromStep before Hinvariant HnotExit)
      as (middle & Hstep).
    pose proof (preserved args fromStep before middle
      Hinvariant HnotExit Hstep) as Hmiddle.
    pose proof (decreases args fromStep before middle
      Hinvariant HnotExit Hstep) as Hdecrease.
    rewrite <- Hbudget in Hdecrease.
    destruct (H _ Hdecrease args (S fromStep) middle Hmiddle eq_refl)
      as (count & after & Hcount & Htrace & Hterminal).
    exists (S count), after. repeat split; try lia.
    + econstructor; eassumption.
    + exact Hterminal.
  - exists 0%nat, before. repeat split.
    + lia.
    + constructor.
    + exists address. auto.
Qed.

Theorem executionCertificateFromDecrease {State Args}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (entry : Args -> State -> Prop)
    (region exitPc : Z -> Prop) (entryPc : Z) (bound : Args -> nat)
    (obligations : DecreasingExecutionObligations
      step pc entry region exitPc entryPc bound) :
  ExecutionPathCertificate step pc entry region exitPc entryPc bound.
Proof.
  constructor.
  - exact (obligationEntryPc _ _ _ _ _ _ _ obligations).
  - intros args fromStep before Hentry.
    pose proof (obligationEntryInvariant _ _ _ _ _ _ _ obligations
      args before Hentry) as Hinvariant.
    destruct (stoppedTerminationFromDecrease step pc region exitPc
      (executionInvariant _ _ _ _ _ _ _ obligations)
      (executionRank _ _ _ _ _ _ _ obligations)
      (obligationPcDefined _ _ _ _ _ _ _ obligations)
      (obligationPcClassified _ _ _ _ _ _ _ obligations)
      (obligationProgress _ _ _ _ _ _ _ obligations)
      (obligationPreservation _ _ _ _ _ _ _ obligations)
      (obligationDecrease _ _ _ _ _ _ _ obligations)
      args fromStep before Hinvariant)
      as (count & after & Hcount & Htrace & Hterminal).
    exists count, after. repeat split; try assumption.
    + destruct count.
      * inversion Htrace; subst after.
        destruct Hterminal as (address & Hpc & Hexit).
        pose proof (obligationEntryPc _ _ _ _ _ _ _ obligations
          args before Hentry) as HentryPc.
        rewrite HentryPc in Hpc. inversion Hpc. subst.
        exact (False_ind _ (obligationEntryNotExit _ _ _ _ _ _ _
          obligations Hexit)).
      * lia.
    + eapply Nat.le_trans; [exact Hcount |].
      exact (obligationEntryBound _ _ _ _ _ _ _ obligations
        args before Hentry).
  - intros args fromStep count before after Hentry Htrace.
    pose proof (obligationEntryInvariant _ _ _ _ _ _ _ obligations
      args before Hentry) as Hinvariant.
    pose proof (stoppedTraceInvariant step pc exitPc
      (executionInvariant _ _ _ _ _ _ _ obligations)
      (obligationPreservation _ _ _ _ _ _ _ obligations)
      args fromStep count before after Hinvariant Htrace) as Hafter.
    split.
    + eapply Nat.le_trans.
      * exact (stoppedTraceRankBound step pc exitPc
          (executionInvariant _ _ _ _ _ _ _ obligations)
          (executionRank _ _ _ _ _ _ _ obligations)
          (obligationPreservation _ _ _ _ _ _ _ obligations)
          (obligationDecrease _ _ _ _ _ _ _ obligations)
          args fromStep count before after Hinvariant Htrace).
      * exact (obligationEntryBound _ _ _ _ _ _ _ obligations
          args before Hentry).
    + destruct (obligationPcDefined _ _ _ _ _ _ _ obligations
        args after Hafter) as (address & Hpc).
      exists address. split; [exact Hpc |].
      destruct (obligationPcClassified _ _ _ _ _ _ _ obligations
        args after address Hafter Hpc) as [[Hregion _] | Hexit]; auto.
  - intros args fromStep count before state Hentry Htrace HnotExit.
    pose proof (obligationEntryInvariant _ _ _ _ _ _ _ obligations
      args before Hentry) as Hinvariant.
    pose proof (stoppedTraceInvariant step pc exitPc
      (executionInvariant _ _ _ _ _ _ _ obligations)
      (obligationPreservation _ _ _ _ _ _ _ obligations)
      args fromStep count before state Hinvariant Htrace) as Hstate.
    eapply obligationProgress; eassumption.
  - intros args fromStep count before state Hentry Htrace Hstuck.
    pose proof (obligationEntryInvariant _ _ _ _ _ _ _ obligations
      args before Hentry) as Hinvariant.
    pose proof (stoppedTraceInvariant step pc exitPc
      (executionInvariant _ _ _ _ _ _ _ obligations)
      (obligationPreservation _ _ _ _ _ _ _ obligations)
      args fromStep count before state Hinvariant Htrace) as Hstate.
    destruct (obligationPcDefined _ _ _ _ _ _ _ obligations
      args state Hstate) as (address & Hpc).
    destruct (obligationPcClassified _ _ _ _ _ _ _ obligations
      args state address Hstate Hpc) as [[Hregion HnotExit] | Hexit].
    + exfalso.
      destruct (obligationProgress _ _ _ _ _ _ _ obligations
        args (fromStep + count)%nat state Hstate)
        as (next & Hstep).
      * intros terminal Hterminal.
        rewrite Hpc in Hterminal. inversion Hterminal. subst. exact HnotExit.
      * exact (Hstuck next Hstep).
    + exists address. auto.
  - intros args fromStep before Hentry (run & Hzero & Hrun).
    subst before.
    pose proof (obligationEntryInvariant _ _ _ _ _ _ _ obligations
      args (run 0) Hentry) as Hinvariant.
    pose proof (infiniteStoppedPrefix step pc exitPc run fromStep
      (S (executionRank _ _ _ _ _ _ _ obligations args (run 0))) Hrun)
      as Hprefix.
    pose proof (stoppedTraceRankBound step pc exitPc
      (executionInvariant _ _ _ _ _ _ _ obligations)
      (executionRank _ _ _ _ _ _ _ obligations)
      (obligationPreservation _ _ _ _ _ _ _ obligations)
      (obligationDecrease _ _ _ _ _ _ _ obligations)
      args fromStep _ (run 0) _ Hinvariant Hprefix).
    lia.
Qed.

Print Assumptions executionCertificateFromDecrease.
