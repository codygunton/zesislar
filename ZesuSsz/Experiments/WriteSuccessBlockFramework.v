From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Import ListNotations.

(** A block invariant relates the Level 1 arguments, a block identifier,
    its symbolic parameters, and the concrete state at the block entry. *)
Definition Inv_ {State Args Block Params : Type} : Type :=
  Args -> Block -> Params -> State -> Prop.

(** [iterate successor count state] computes the state after [count]
    applications of the block's covered successor. *)
Fixpoint iterate {State : Type} (successor : State -> State)
    (count : nat) (state : State) : State :=
  match count with
  | O => state
  | S count' => iterate successor count' (successor state)
  end.

Lemma iterate_zero {State} (successor : State -> State) state :
  iterate successor 0 state = state.
Proof. reflexivity. Qed.

Lemma iterate_succ {State} (successor : State -> State) count state :
  iterate successor (S count) state =
    successor (iterate successor count state).
Proof.
  revert state. induction count as [|count IH]; intros state.
  - reflexivity.
  - change (iterate successor (S count) (successor state) =
      successor (iterate successor count (successor state))).
    apply IH.
Qed.

Lemma iterate_add {State} (successor : State -> State) first second state :
  iterate successor (first + second) state =
    iterate successor second (iterate successor first state).
Proof.
  revert state. induction first as [|first IH]; intros state; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** An execution state lies at a strict offset inside one represented block.
    The successor is a function because the coverage lemma identifies every
    relational step with that function. *)
Definition blockExecutionInvariant {State Args Block Params : Type}
    (blockInvariant : Inv_)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State)
    (args : Args) (state : State) : Prop :=
  exists block params offset entryState,
    blockInvariant args block params entryState /\
    entryConsistent args entryState /\
    offset < blockLength block /\
    state = iterate (blockSuccessor args block params) offset entryState.

Lemma blockExecutionInvariantAtEntry {State Args Block Params}
    (blockInvariant : @Inv_ State Args Block Params)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State)
    args block params entryState :
  blockInvariant args block params entryState ->
  entryConsistent args entryState ->
  0 < blockLength block ->
  blockExecutionInvariant blockInvariant entryConsistent blockLength blockSuccessor
    args entryState.
Proof.
  intros Hinvariant Hconsistent Hlength.
  exists block, params, 0%nat, entryState. repeat split; try assumption.
Qed.

Lemma blockExecutionInvariantAdvance {State Args Block Params}
    (blockInvariant : @Inv_ State Args Block Params)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State)
    args block params offset entryState :
  blockInvariant args block params entryState ->
  entryConsistent args entryState ->
  S offset < blockLength block ->
  blockExecutionInvariant blockInvariant entryConsistent blockLength blockSuccessor args
    (iterate (blockSuccessor args block params) (S offset) entryState).
Proof.
  intros Hinvariant Hconsistent Hoffset.
  exists block, params, (S offset), entryState. auto.
Qed.

(** Instruction runs compose without changing their segment evidence. *)
Lemma islaInstructionRun_app firstCount secondCount before first middle
    second after :
  IslaInstructionRun firstCount before first middle ->
  IslaInstructionRun secondCount middle second after ->
  IslaInstructionRun (firstCount + secondCount) before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; simpl; first exact Hsecond.
  econstructor; eauto.
Qed.

Lemma islaInstructionRun_snoc count before segments middle observations after :
  IslaInstructionRun count before segments middle ->
  IslaInstructionSegment middle observations after ->
  IslaInstructionRun (S count) before (segments ++ [observations]) after.
Proof.
  intros Hrun Hsegment.
  replace (S count) with (count + 1)%nat by lia.
  eapply islaInstructionRun_app; first exact Hrun.
  econstructor; [exact Hsegment | constructor].
Qed.

(** A rank decrease composes across a computed sequence of successors. *)
Lemma iterate_rank_decreases {State Args}
    (successor : Args -> State -> State) (rank : Args -> State -> nat) :
  (forall args state,
    (rank args (successor args state) < rank args state)%nat) ->
  forall args count state,
    (rank args (iterate (successor args) count state) + count <=
      rank args state)%nat.
Proof.
  intros Hdecrease args count. induction count as [|count IH]; intros state.
  - simpl. lia.
  - simpl. specialize (IH (successor args state)).
    specialize (Hdecrease args state). lia.
Qed.

Lemma rank_composition firstCount secondCount firstRank middleRank lastRank :
  (middleRank + firstCount <= firstRank)%nat ->
  (lastRank + secondCount <= middleRank)%nat ->
  (lastRank + (firstCount + secondCount) <= firstRank)%nat.
Proof. lia. Qed.

Lemma blockInvariantPreserved {State Args Block Params : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (exitPc : Z -> Prop)
    (blockInvariant : @Inv_ State Args Block Params)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State) :
  (forall args block params offset entryState index after,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    step index
      (iterate (blockSuccessor args block params) offset entryState) after ->
    after =
      iterate (blockSuccessor args block params) (S offset) entryState) ->
  (forall args block params entryState,
    blockInvariant args block params entryState ->
    exists nextBlock nextParams,
      blockInvariant args nextBlock nextParams
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      entryConsistent args
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      0 < blockLength nextBlock) ->
  forall args index before after,
    blockExecutionInvariant blockInvariant entryConsistent blockLength blockSuccessor
      args before ->
    (forall address, pc before = Some address -> ~ exitPc address) ->
    step index before after ->
    blockExecutionInvariant blockInvariant entryConsistent blockLength blockSuccessor
      args after.
Proof.
  intros Hcovered Hhandoff args index before after
    (block & params & offset & entryState & Hinvariant & Hconsistent & Hoffset & ->)
    HnotExit Hstep.
  pose proof (Hcovered args block params offset entryState index after
    Hinvariant Hoffset Hstep) as ->.
  destruct (Nat.lt_ge_cases (S offset) (blockLength block)) as [Hinside|Hend].
    - eapply blockExecutionInvariantAdvance; eassumption.
  - assert (S offset = blockLength block) by lia. subst.
    destruct (Hhandoff args block params entryState Hinvariant)
      as (nextBlock & nextParams & Hnext & HnextConsistent & Hlength).
    exists nextBlock, nextParams, 0%nat,
      (iterate (blockSuccessor args block params)
        (blockLength block) entryState).
    repeat split; try assumption.
    now rewrite H.
Qed.

Lemma blockRankPreservedDecrease {State Args Block Params : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (exitPc : Z -> Prop)
    (blockInvariant : @Inv_ State Args Block Params)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State)
    (rank : Args -> State -> nat) :
  (forall args block params offset entryState index after,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    step index
      (iterate (blockSuccessor args block params) offset entryState) after ->
    after =
      iterate (blockSuccessor args block params) (S offset) entryState) ->
  (forall args block params offset entryState,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    (forall address,
      pc (iterate (blockSuccessor args block params) offset entryState) =
        Some address -> ~ exitPc address) ->
    (rank args
        (iterate (blockSuccessor args block params) (S offset) entryState) <
     rank args
        (iterate (blockSuccessor args block params) offset entryState))%nat) ->
  forall args index before after,
    blockExecutionInvariant blockInvariant entryConsistent blockLength blockSuccessor
      args before ->
    (forall address, pc before = Some address -> ~ exitPc address) ->
    step index before after ->
    (rank args after < rank args before)%nat.
Proof.
  intros Hcovered Hdecrease args index before after
    (block & params & offset & entryState & Hinvariant & Hconsistent & Hoffset & ->)
    HnotExit Hstep.
  pose proof (Hcovered args block params offset entryState index after
    Hinvariant Hoffset Hstep) as ->.
  eapply Hdecrease; eassumption.
Qed.

Theorem decreasingExecutionObligationsFromBlocks
    {State Args Block Params : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z) (entry : Args -> State -> Prop)
    (region exitPc : Z -> Prop) (entryPc : Z) (bound : Args -> nat)
    (blockInvariant : @Inv_ State Args Block Params)
    (entryConsistent : Args -> State -> Prop)
    (blockLength : Block -> nat)
    (blockSuccessor : Args -> Block -> Params -> State -> State)
    (rank : Args -> State -> nat) :
  (forall args state, entry args state -> pc state = Some entryPc) ->
  ~ exitPc entryPc ->
  (forall args state,
    entry args state ->
    exists block params,
      blockInvariant args block params state /\
      entryConsistent args state /\
      0 < blockLength block) ->
  (forall args block params offset entryState,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    exists address,
      pc (iterate (blockSuccessor args block params) offset entryState) =
        Some address) ->
  (forall args block params offset entryState address,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    pc (iterate (blockSuccessor args block params) offset entryState) =
      Some address ->
    (region address /\ ~ exitPc address) \/ exitPc address) ->
  (forall args block params offset entryState index,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    (forall address,
      pc (iterate (blockSuccessor args block params) offset entryState) =
        Some address -> ~ exitPc address) ->
    step index
      (iterate (blockSuccessor args block params) offset entryState)
      (iterate (blockSuccessor args block params) (S offset) entryState)) ->
  (forall args block params offset entryState index after,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    step index
      (iterate (blockSuccessor args block params) offset entryState) after ->
    after =
      iterate (blockSuccessor args block params) (S offset) entryState) ->
  (forall args block params entryState,
    blockInvariant args block params entryState ->
    exists nextBlock nextParams,
      blockInvariant args nextBlock nextParams
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      entryConsistent args
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      0 < blockLength nextBlock) ->
  (forall args block params offset entryState,
    blockInvariant args block params entryState ->
    offset < blockLength block ->
    (forall address,
      pc (iterate (blockSuccessor args block params) offset entryState) =
        Some address -> ~ exitPc address) ->
    (rank args
        (iterate (blockSuccessor args block params) (S offset) entryState) <
     rank args
        (iterate (blockSuccessor args block params) offset entryState))%nat) ->
  (forall args state,
    entry args state -> (rank args state <= bound args)%nat) ->
  DecreasingExecutionObligations step pc entry region exitPc entryPc bound.
Proof.
  intros HentryPc HentryNotExit HentryBlock Hdefined Hclassified
    Hexists Hcovered Hhandoff Hdecrease Hbound.
  refine {| executionInvariant :=
      blockExecutionInvariant blockInvariant entryConsistent blockLength
        blockSuccessor;
    executionRank := rank |}.
  - exact HentryPc.
  - exact HentryNotExit.
  - intros args state Hentry.
    destruct (HentryBlock args state Hentry)
      as (block & params & Hinvariant & Hconsistent & Hlength).
    eapply blockExecutionInvariantAtEntry; eassumption.
  - intros args state
      (block & params & offset & entryState & Hinvariant & Hconsistent &
       Hoffset & ->).
    eapply Hdefined; eassumption.
  - intros args state address
      (block & params & offset & entryState & Hinvariant & Hconsistent &
       Hoffset & ->) Hpc.
    eapply Hclassified; eassumption.
  - intros args index state
      (block & params & offset & entryState & Hinvariant & Hconsistent &
       Hoffset & ->)
      HnotExit.
    eexists. eapply Hexists; eassumption.
  - eapply blockInvariantPreserved; eassumption.
  - eapply blockRankPreservedDecrease; eassumption.
  - exact Hbound.
Qed.

Print Assumptions iterate_add.
Print Assumptions iterate_zero.
Print Assumptions iterate_succ.
Print Assumptions blockExecutionInvariantAtEntry.
Print Assumptions blockExecutionInvariantAdvance.
Print Assumptions islaInstructionRun_app.
Print Assumptions islaInstructionRun_snoc.
Print Assumptions iterate_rank_decreases.
Print Assumptions rank_composition.
Print Assumptions blockInvariantPreserved.
Print Assumptions blockRankPreservedDecrease.
Print Assumptions decreasingExecutionObligationsFromBlocks.
