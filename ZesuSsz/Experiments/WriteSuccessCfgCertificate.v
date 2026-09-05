From Coq Require Import Lists.List ZArith.ZArith.
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

(** This record separates the finite witness consumed by the existing bridge
    from the universal bounded-path obligation.  A cyclic CFG must supply a
    ranking or explicit loop budgets to prove [writeSuccessCfgAllPaths]. *)
Record WriteSuccessCfgCertificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Type := {
  writeSuccessCfgWitness :
    InstructionPathCertificate nextPc region exitPc entryPc bound;
  writeSuccessCfgRankWitness : Z -> nat;
  writeSuccessCfgRankProof :
    writeSuccessCfgRanked nextPc region writeSuccessCfgRankWitness;
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
    (rank : Z -> nat)
    (Hrank : writeSuccessCfgRanked nextPc region rank)
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
            writeSuccessCfgRankWitness := rank;
            writeSuccessCfgRankProof := Hrank;
            writeSuccessCfgNoInfinite := writeSuccessCfgRanked_no_infinite
              nextPc region rank Hrank |}.
  intros path Hpath Hmax.
  apply Hall; [|exact Hmax].
  split; [exact Hpath |].
  intros edge Hedge.
  apply Hbudget; assumption.
Qed.
