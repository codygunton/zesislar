From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import ZesuSsz.Contracts.Machine.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessCfgBackEdges : list (Z * Z) := [
  (0x153b4, 0x151d4); (0x153a8, 0x15228);
  (0x15558, 0x153d4); (0x15614, 0x15590);
  (0x1565c, 0x14f00); (0x156dc, 0x15694);
  (0x158d4, 0x15754)
].

Fixpoint writeSuccessCfgEdgeHitsTail
    (edge : Z * Z) (fromPc : Z) (path : list Z) : nat :=
  match path with
  | toPc :: rest =>
      (if Z.eq_dec fromPc (fst edge)
       then if Z.eq_dec toPc (snd edge) then 1 else 0
       else 0) +
      writeSuccessCfgEdgeHitsTail edge toPc rest
  | [] => 0
  end.

Definition writeSuccessCfgEdgeHits
    (edge : Z * Z) (path : list Z) : nat :=
  match path with
  | fromPc :: rest => writeSuccessCfgEdgeHitsTail edge fromPc rest
  | [] => 0
  end.

(** A path in the generated writeSuccess CFG.  The path contains block entry
    PCs, while [Forall] excludes its terminal exit PC. *)
Definition writeSuccessCfgPath
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (path : list Z) : Prop :=
  hd_error path = Some entryPc /\
  InstructionPathFollows nextPc path /\
  Forall region (removelast path).

Definition writeSuccessCfgBudgetedPath
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (budget : (Z * Z) -> nat) (path : list Z) : Prop :=
  writeSuccessCfgPath nextPc region exitPc entryPc path /\
  (forall edge, In edge writeSuccessCfgBackEdges ->
    writeSuccessCfgEdgeHits edge path <= budget edge)%nat.

(** A maximal path has no outgoing edge after its final PC.  This condition
    makes the universal claim stronger than a single selected execution. *)
Definition writeSuccessCfgMaximal
    (nextPc : Z -> Z -> Prop) (exitPc : Z -> Prop)
    (path : list Z) : Prop :=
  exists pc, last path 0%Z = pc /\
    (exitPc pc \/ forall next, ~ nextPc pc next).

(** The PC relation alone cannot express loop progress.  This control state
    carries one fuel value and the seven loop counters. *)
Record WriteSuccessControlState : Type := {
  writeSuccessControlPc : Z;
  writeSuccessHashesRemaining : nat;
  writeSuccessBlobHashesRemaining : nat;
  writeSuccessStorageKeysRemaining : nat;
  writeSuccessWithdrawalsRemaining : nat;
  writeSuccessAuthorizationsRemaining : nat;
  writeSuccessAccessListsRemaining : nat;
  writeSuccessTransactionsRemaining : nat;
  writeSuccessControlFuel : nat
}.

Definition writeSuccessControlRank (state : WriteSuccessControlState) : nat :=
  writeSuccessControlFuel state +
  writeSuccessHashesRemaining state +
  writeSuccessBlobHashesRemaining state +
  writeSuccessStorageKeysRemaining state +
  writeSuccessWithdrawalsRemaining state +
  writeSuccessAuthorizationsRemaining state +
  writeSuccessAccessListsRemaining state +
  writeSuccessTransactionsRemaining state.

Definition writeSuccessControlStep
    (nextPc : Z -> Z -> Prop)
    (fromState toState : WriteSuccessControlState) : Prop :=
  nextPc (writeSuccessControlPc fromState) (writeSuccessControlPc toState) /\
  (writeSuccessControlFuel toState < writeSuccessControlFuel fromState)%nat /\
  (writeSuccessHashesRemaining toState <= writeSuccessHashesRemaining fromState)%nat /\
  (writeSuccessBlobHashesRemaining toState <= writeSuccessBlobHashesRemaining fromState)%nat /\
  (writeSuccessStorageKeysRemaining toState <= writeSuccessStorageKeysRemaining fromState)%nat /\
  (writeSuccessWithdrawalsRemaining toState <= writeSuccessWithdrawalsRemaining fromState)%nat /\
  (writeSuccessAuthorizationsRemaining toState <= writeSuccessAuthorizationsRemaining fromState)%nat /\
  (writeSuccessAccessListsRemaining toState <= writeSuccessAccessListsRemaining fromState)%nat /\
  (writeSuccessTransactionsRemaining toState <= writeSuccessTransactionsRemaining fromState)%nat.

Lemma writeSuccessControlStep_rank
    (nextPc : Z -> Z -> Prop) fromState toState :
  writeSuccessControlStep nextPc fromState toState ->
  (writeSuccessControlRank toState < writeSuccessControlRank fromState)%nat.
Proof.
  intros H.
  destruct H as (Hpc & Hfuel & Hhash & Hblob & Hstorage & Hwithdrawals &
    Hauth & Haccess & Htransactions).
  unfold writeSuccessControlRank.
  lia.
Qed.

Inductive writeSuccessControlPath
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop) :
    list WriteSuccessControlState -> Prop :=
| WriteSuccessControlPathOne state :
    writeSuccessControlPath stateStep [state]
| WriteSuccessControlPathNext fromState toState rest :
    stateStep fromState toState ->
    writeSuccessControlPath stateStep (toState :: rest) ->
    writeSuccessControlPath stateStep (fromState :: toState :: rest).

Lemma writeSuccessControlPath_project
    (nextPc : Z -> Z -> Prop)
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop) :
  (forall fromState toState, stateStep fromState toState ->
    nextPc (writeSuccessControlPc fromState) (writeSuccessControlPc toState)) ->
  forall states, writeSuccessControlPath stateStep states ->
    InstructionPathFollows nextPc (List.map writeSuccessControlPc states).
Proof.
  intros Hproject states Hstates.
  induction Hstates as [state | fromState toState rest Hstep Hrest IH].
  - constructor.
  - simpl. apply InstructionPathNext.
    + apply Hproject; assumption.
    + exact IH.
Qed.

(** This lemma is the explicit handoff from a ranked state path to the PC
    witness consumed by [nativeContractBridge].  The caller must provide the
    state invariant facts for the projected path. *)
Lemma writeSuccessControlPath_project_certificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat)
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop)
    (Hproject : forall fromState toState, stateStep fromState toState ->
      nextPc (writeSuccessControlPc fromState)
        (writeSuccessControlPc toState))
    (states : list WriteSuccessControlState)
    (Hstates : writeSuccessControlPath stateStep states)
    (Hhead : hd_error (List.map writeSuccessControlPc states) = Some entryPc)
    (Hregion : Forall region
      (removelast (List.map writeSuccessControlPc states)))
    (Hexit : exists pc,
      last (List.map writeSuccessControlPc states) entryPc = pc /\ exitPc pc)
    (Hlength : length states = S bound)
    (Hbound : (0 < bound)%nat) :
  InstructionPathCertificate nextPc region exitPc entryPc bound.
Proof.
  exists (List.map writeSuccessControlPc states).
  repeat split.
  - exact Hhead.
  - apply (writeSuccessControlPath_project nextPc stateStep).
    + exact Hproject.
    + exact Hstates.
  - exact Hregion.
  - exact Hexit.
  - rewrite map_length.
    exact Hlength.
  - exact Hbound.
Qed.

(** These are the concrete obligations for a future writeSuccess witness.
    The current loop invariants must instantiate seven counter bounds and
    show progress on every back edge.  A static instruction count does not
    discharge any of these inequalities. *)
Record WriteSuccessLoopCounterObligations
    (stateInvariant : WriteSuccessControlState -> Prop)
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop)
    (entryState : WriteSuccessControlState)
    (bound : nat) : Prop := {
  writeSuccessEntryStateInvariant : stateInvariant entryState;
  writeSuccessEntryStatePc :
    writeSuccessControlPc entryState = 0x14d30;
  writeSuccessEntryRankBound :
    (writeSuccessControlRank entryState <= bound)%nat;
  writeSuccessStateInvariantPreserved :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      stateInvariant toState;
  writeSuccessFuelProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessControlFuel toState <
       writeSuccessControlFuel fromState)%nat;
  writeSuccessHashesProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessHashesRemaining toState <=
       writeSuccessHashesRemaining fromState)%nat;
  writeSuccessBlobHashesProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessBlobHashesRemaining toState <=
       writeSuccessBlobHashesRemaining fromState)%nat;
  writeSuccessStorageKeysProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessStorageKeysRemaining toState <=
       writeSuccessStorageKeysRemaining fromState)%nat;
  writeSuccessWithdrawalsProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessWithdrawalsRemaining toState <=
       writeSuccessWithdrawalsRemaining fromState)%nat;
  writeSuccessAuthorizationsProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessAuthorizationsRemaining toState <=
       writeSuccessAuthorizationsRemaining fromState)%nat;
  writeSuccessAccessListsProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessAccessListsRemaining toState <=
       writeSuccessAccessListsRemaining fromState)%nat;
  writeSuccessTransactionsProgress :
    forall fromState toState,
      stateInvariant fromState -> stateStep fromState toState ->
      (writeSuccessTransactionsRemaining toState <=
       writeSuccessTransactionsRemaining fromState)%nat
}.

(** A bounded execution consumes one natural-number unit at every successor.
    The inductive definition has no constructor for an infinite execution. *)
Inductive writeSuccessCfgRun
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop) :
    nat -> list Z -> Prop :=
| WriteSuccessCfgRunExit pc :
    exitPc pc -> writeSuccessCfgRun nextPc region exitPc 0 [pc]
| WriteSuccessCfgRunStep fuel fromPc toPc rest :
    region fromPc ->
    nextPc fromPc toPc ->
    writeSuccessCfgRun nextPc region exitPc fuel (toPc :: rest) ->
    writeSuccessCfgRun nextPc region exitPc (S fuel) (fromPc :: toPc :: rest).

(** A rank decreases on every allowed transition.  This is the well-founded
    obligation that excludes an infinite cycle.  For machine loops, the rank
    must include the loop counters or input index; a rank on PC alone cannot
    satisfy this condition for the seven cyclic CFG edges. *)
Definition writeSuccessCfgRanked
    (nextPc : Z -> Z -> Prop) (region : Z -> Prop)
    (rank : Z -> nat) : Prop :=
  forall fromPc toPc,
    region fromPc -> nextPc fromPc toPc -> (rank toPc < rank fromPc)%nat.

Definition writeSuccessCfgNoInfinitePath
    (nextPc : Z -> Z -> Prop) (region : Z -> Prop) : Prop :=
  forall path : nat -> Z,
    (forall index, region (path index)) ->
    (forall index, nextPc (path index) (path (S index))) -> False.

Lemma writeSuccessCfgRanked_no_infinite
    (nextPc : Z -> Z -> Prop) (region : Z -> Prop)
    (rank : Z -> nat) :
  writeSuccessCfgRanked nextPc region rank ->
  writeSuccessCfgNoInfinitePath nextPc region.
Proof.
  intros Hrank path Hregion Hstep.
  remember (rank (path 0%nat)) as initialRank eqn:Hinitial.
  revert path Hregion Hstep Hinitial.
  induction initialRank using lt_wf_ind.
  intros path Hregion Hstep Hinitial.
  pose proof (Hrank (path 0%nat) (path 1%nat)
    (Hregion 0%nat) (Hstep 0%nat)) as Hdecrease.
  rewrite <- Hinitial in Hdecrease.
  apply (H _ Hdecrease (fun index => path (S index))).
  - intros index. exact (Hregion (S index)).
  - intros index. exact (Hstep (S index)).
  - reflexivity.
Qed.

Lemma writeSuccessStateRanked_no_infinite
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop)
    (rank : WriteSuccessControlState -> nat) :
  (forall fromState toState, stateStep fromState toState ->
    (rank toState < rank fromState)%nat) ->
  forall path : nat -> WriteSuccessControlState,
    (forall index, stateStep (path index) (path (S index))) -> False.
Proof.
  intros Hrank path Hstep.
  remember (rank (path 0%nat)) as initialRank eqn:Hinitial.
  revert path Hstep Hinitial.
  induction initialRank using lt_wf_ind.
  intros path Hstep Hinitial.
  pose proof (Hrank (path 0%nat) (path 1%nat) (Hstep 0%nat)) as Hdecrease.
  rewrite <- Hinitial in Hdecrease.
  apply (H _ Hdecrease (fun index => path (S index))).
  - intros index. exact (Hstep (S index)).
  - reflexivity.
Qed.

Lemma writeSuccessControlStep_no_infinite
    (nextPc : Z -> Z -> Prop) :
  forall path : nat -> WriteSuccessControlState,
    (forall index, writeSuccessControlStep nextPc
      (path index) (path (S index))) -> False.
Proof.
  intros path Hstep.
  exact ((writeSuccessStateRanked_no_infinite
    (writeSuccessControlStep nextPc)
    writeSuccessControlRank (writeSuccessControlStep_rank nextPc))
    path Hstep).
Qed.

Lemma writeSuccessStateCoverage_no_infinite
    (nextPc : Z -> Z -> Prop) (region : Z -> Prop)
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop)
    (rank : WriteSuccessControlState -> nat)
    (Hrank : forall fromState toState, stateStep fromState toState ->
      (rank toState < rank fromState)%nat)
    (Hcoverage : forall path : nat -> Z,
      (forall index, region (path index)) ->
      (forall index, nextPc (path index) (path (S index))) ->
      exists statePath : nat -> WriteSuccessControlState,
        (forall index,
          writeSuccessControlPc (statePath index) = path index) /\
        (forall index,
          stateStep (statePath index) (statePath (S index)))) :
  writeSuccessCfgNoInfinitePath nextPc region.
Proof.
  intros path Hregion Hnext.
  destruct (Hcoverage path Hregion Hnext) as [statePath [_ Hstate]].
  exact ((writeSuccessStateRanked_no_infinite stateStep rank Hrank)
    statePath Hstate).
Qed.

(** This record separates the finite witness consumed by the existing bridge
    from the universal bounded-path obligation.  A cyclic CFG must supply a
    ranking or explicit loop budgets to prove [writeSuccessCfgAllPaths]. *)
Record WriteSuccessCfgCertificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Type := {
  writeSuccessCfgWitness :
    InstructionPathCertificate nextPc region exitPc entryPc bound;
  writeSuccessCfgStateStep :
    WriteSuccessControlState -> WriteSuccessControlState -> Prop;
  writeSuccessCfgStateRankProof :
    forall fromState toState,
      writeSuccessCfgStateStep fromState toState ->
      (writeSuccessControlRank toState <
       writeSuccessControlRank fromState)%nat;
  writeSuccessCfgStateProjection :
    forall fromState toState,
      writeSuccessCfgStateStep fromState toState ->
        nextPc (writeSuccessControlPc fromState)
        (writeSuccessControlPc toState);
  writeSuccessCfgStateCoverage :
    forall path : nat -> Z,
      (forall index, region (path index)) ->
      (forall index, nextPc (path index) (path (S index))) ->
      exists statePath : nat -> WriteSuccessControlState,
        (forall index,
          writeSuccessControlPc (statePath index) = path index) /\
        (forall index, writeSuccessCfgStateStep
          (statePath index) (statePath (S index)));
  writeSuccessCfgNoInfinite : writeSuccessCfgNoInfinitePath nextPc region;
  writeSuccessCfgAllPaths :
    forall path,
      writeSuccessCfgPath nextPc region exitPc entryPc path ->
      writeSuccessCfgMaximal nextPc exitPc path ->
      exists pc, last path 0%Z = pc /\ exitPc pc /\
        (length path <= S bound)%nat /\
        exists fuel : nat, (fuel <= bound)%nat /\
          writeSuccessCfgRun nextPc region exitPc fuel path
}.

Lemma writeSuccessCfgCertificateBridge
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) :
  WriteSuccessCfgCertificate nextPc region exitPc entryPc bound ->
  correctness ->
  NativeContractAssumption correctness nextPc region exitPc entryPc bound.
Proof.
  intros certificate Hcorrect.
  apply nativeContractBridge; [exact Hcorrect |].
  exact (writeSuccessCfgWitness nextPc region exitPc entryPc bound certificate).
Qed.

(** A budgeted-path relation is sufficient when it proves that every maximal
    path stays within each loop budget and reaches the declared exit. *)
Definition writeSuccessCfgBudgetedPathRelation
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (budget : (Z * Z) -> nat) (bound : nat) : Prop :=
  forall path,
    writeSuccessCfgBudgetedPath nextPc region exitPc entryPc budget path ->
    writeSuccessCfgMaximal nextPc exitPc path ->
    exists pc, last path 0%Z = pc /\ exitPc pc /\
      (length path <= S bound)%nat /\
      exists fuel : nat, (fuel <= bound)%nat /\
        writeSuccessCfgRun nextPc region exitPc fuel path.

Lemma writeSuccessCfgBudgetedPath_implies_certificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (budget : (Z * Z) -> nat) (bound : nat)
    (stateStep : WriteSuccessControlState -> WriteSuccessControlState -> Prop)
    (Hrank : forall fromState toState, stateStep fromState toState ->
      (writeSuccessControlRank toState <
       writeSuccessControlRank fromState)%nat)
    (Hproject : forall fromState toState, stateStep fromState toState ->
      nextPc (writeSuccessControlPc fromState)
        (writeSuccessControlPc toState))
    (Hcoverage : forall path : nat -> Z,
      (forall index, region (path index)) ->
      (forall index, nextPc (path index) (path (S index))) ->
      exists statePath : nat -> WriteSuccessControlState,
        (forall index,
          writeSuccessControlPc (statePath index) = path index) /\
        (forall index, stateStep (statePath index) (statePath (S index))))
    (Hbudget : forall path,
      writeSuccessCfgPath nextPc region exitPc entryPc path ->
      writeSuccessCfgMaximal nextPc exitPc path ->
      forall edge, In edge writeSuccessCfgBackEdges ->
        (writeSuccessCfgEdgeHits edge path <= budget edge)%nat)
    (Hwitness : InstructionPathCertificate nextPc region exitPc entryPc bound) :
  writeSuccessCfgBudgetedPathRelation nextPc region exitPc entryPc budget bound ->
  WriteSuccessCfgCertificate nextPc region exitPc entryPc bound.
Proof.
  intros Hall.
  refine {| writeSuccessCfgWitness := Hwitness;
            writeSuccessCfgStateStep := stateStep;
            writeSuccessCfgStateRankProof := Hrank;
            writeSuccessCfgStateProjection := Hproject;
            writeSuccessCfgStateCoverage := Hcoverage;
            writeSuccessCfgNoInfinite := _ |}.
  apply (writeSuccessStateCoverage_no_infinite nextPc region stateStep
    writeSuccessControlRank Hrank Hcoverage).
  intros path Hpath Hmax.
  apply Hall; [|exact Hmax].
  split; [exact Hpath |].
  intros edge Hedge.
  apply Hbudget; assumption.
Qed.
