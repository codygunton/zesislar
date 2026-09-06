From Coq Require Import Lists.List Lia.
Require Import isla.opsem.

Import ListNotations.

Definition IslaState : Type := (seq_local_state * seq_global_state)%type.

Record IslaMicroObservation := {
  microLabels : list seq_label;
  microAfter : IslaState
}.

Inductive IslaMicroPath : IslaState -> list IslaMicroObservation -> IslaState -> Prop :=
| IslaMicroPathRefl state : IslaMicroPath state [] state
| IslaMicroPathStep before labels middleLocal middleGlobal observations after spawned :
    seq_step before.1 before.2 labels middleLocal middleGlobal spawned ->
    IslaMicroPath (middleLocal, middleGlobal) observations after ->
    IslaMicroPath before
      ({| microLabels := labels;
          microAfter := (middleLocal, middleGlobal) |} :: observations) after.

(** An instruction prefix stops before the first [LDone] transition.  A
    [seq_step] whose source trace is [tnil] is exactly such a transition. *)
Inductive IslaInstructionPrefixPath :
    IslaState -> list IslaMicroObservation -> IslaState -> Prop :=
| IslaInstructionPrefixRefl state :
    IslaInstructionPrefixPath state [] state
| IslaInstructionPrefixStep before labels middleLocal middleGlobal
    observations after spawned :
    before.1.(seq_trace) <> tnil ->
    seq_step before.1 before.2 labels middleLocal middleGlobal spawned ->
    IslaInstructionPrefixPath
      (middleLocal, middleGlobal) observations after ->
    IslaInstructionPrefixPath before
      ({| microLabels := labels;
          microAfter := (middleLocal, middleGlobal) |} :: observations) after.

Definition IslaInstructionBoundary (state : IslaState) : Prop :=
  state.1.(seq_nb_state) = false /\
  exists (pc : bv 64) trace,
    state.1.(seq_regs) !! state.1.(seq_pc_reg) =
      Some (RVal_Bits (@bv_to_bvn 64 pc)) /\
    state.2.(seq_instrs) !! pc = Some trace /\
    state.1.(seq_trace) = trace.

Definition IslaInstructionTrap (state : IslaState) : Prop :=
  state.1.(seq_nb_state) = true.

Definition IslaNoEarlyBoundary (observations : list IslaMicroObservation) : Prop :=
  forall prefix observation suffix,
    observations = prefix ++ observation :: suffix ->
    suffix <> [] ->
    ~ IslaInstructionBoundary observation.(microAfter) /\
      ~ IslaInstructionTrap observation.(microAfter).

Record IslaInstructionSegment
    (before : IslaState) (observations : list IslaMicroObservation)
    (after : IslaState) : Prop := {
  instructionSegmentStart : IslaInstructionBoundary before;
  instructionSegmentDoneSource : IslaState;
  instructionSegmentPrefix : list IslaMicroObservation;
  instructionSegmentLabels : list seq_label;
  instructionSegmentSpawned : list seq_local_state;
  instructionSegmentPrefixPath :
    IslaInstructionPrefixPath before instructionSegmentPrefix
      instructionSegmentDoneSource;
  instructionSegmentAtDone :
    instructionSegmentDoneSource.1.(seq_trace) = tnil;
  instructionSegmentDoneStep :
    seq_step instructionSegmentDoneSource.1 instructionSegmentDoneSource.2
      instructionSegmentLabels after.1 after.2 instructionSegmentSpawned;
  instructionSegmentObservations :
    observations = instructionSegmentPrefix ++
      (({| microLabels := instructionSegmentLabels; microAfter := after |}) :: []);
  instructionSegmentEnd :
    IslaInstructionBoundary after \/ IslaInstructionTrap after
}.

Inductive IslaInstructionRun :
    nat -> IslaState -> list (list IslaMicroObservation) -> IslaState -> Prop :=
| IslaInstructionRunZero state : IslaInstructionRun 0 state [] state
| IslaInstructionRunStep count before observations middle segments after :
    IslaInstructionSegment before observations middle ->
    IslaInstructionRun count middle segments after ->
    IslaInstructionRun (S count) before (observations :: segments) after.

Inductive IslaStoppedInstructionRun (exitState : IslaState -> Prop) :
    nat -> IslaState -> list (list IslaMicroObservation) -> IslaState -> Prop :=
| IslaStoppedInstructionRunExit state :
    exitState state -> IslaStoppedInstructionRun exitState 0 state [] state
| IslaStoppedInstructionRunStep count before observations middle segments after :
    ~ exitState before ->
    IslaInstructionSegment before observations middle ->
    IslaStoppedInstructionRun exitState count middle segments after ->
    IslaStoppedInstructionRun exitState (S count) before
      (observations :: segments) after.

Fixpoint flattenMicroObservations
    (segments : list (list IslaMicroObservation)) : list IslaMicroObservation :=
  match segments with
  | [] => []
  | segment :: rest => segment ++ flattenMicroObservations rest
  end.

Lemma islaMicroPathAppend before first middle second after :
  IslaMicroPath before first middle ->
  IslaMicroPath middle second after ->
  IslaMicroPath before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; simpl; first assumption.
  econstructor; eauto.
Qed.

Lemma islaInstructionPrefixCorrespondence before observations after :
  IslaInstructionPrefixPath before observations after ->
  IslaMicroPath before observations after.
Proof.
  intros Hpath. induction Hpath; first constructor.
  econstructor; eauto.
Qed.

Lemma islaInstructionSegmentCorrespondence before observations after :
  IslaInstructionSegment before observations after ->
  IslaMicroPath before observations after.
Proof.
  intros Hsegment.
  destruct Hsegment as
    [Hstart doneSource prefix labels spawned Hprefix HatDone Hdone -> Hend].
  destruct doneSource as [doneLocal doneGlobal].
  destruct after as [afterLocal afterGlobal].
  cbn in *.
  eapply islaMicroPathAppend.
  - exact (islaInstructionPrefixCorrespondence _ _ _ Hprefix).
  - econstructor; [exact Hdone | constructor].
Qed.

Lemma islaInstructionRunCorrespondence count before segments after :
  IslaInstructionRun count before segments after ->
  IslaMicroPath before (flattenMicroObservations segments) after.
Proof.
  intros Hrun. induction Hrun; simpl; first constructor.
  eapply islaMicroPathAppend; eauto using islaInstructionSegmentCorrespondence.
Qed.

Lemma islaInstructionRunCount count before segments after :
  IslaInstructionRun count before segments after ->
  length segments = count.
Proof. intros Hrun. induction Hrun; simpl; congruence. Qed.

Lemma islaInstructionSegmentHasMicroStep before observations after :
  IslaInstructionSegment before observations after ->
  exists first rest, observations = first :: rest.
Proof.
  intros Hsegment. destruct observations as [|first rest].
  - destruct Hsegment as
      [Hstart doneSource prefix labels spawned Hprefix HatDone Hdone
       Hobservations Hend].
    destruct prefix; discriminate Hobservations.
  - eauto.
Qed.

Lemma islaInstructionSegmentIntro before prefix done labels after spawned :
  IslaInstructionBoundary before ->
  IslaInstructionPrefixPath before prefix done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  (IslaInstructionBoundary after \/ IslaInstructionTrap after) ->
  IslaInstructionSegment before
    (prefix ++ (({| microLabels := labels; microAfter := after |}) :: []))
    after.
Proof.
  intros Hbefore Hprefix HdoneTrace HdoneStep Hafter.
  eapply Build_IslaInstructionSegment with
    (instructionSegmentDoneSource := done)
    (instructionSegmentPrefix := prefix)
    (instructionSegmentLabels := labels)
    (instructionSegmentSpawned := spawned); eauto.
Qed.

Lemma seqStepSourceBlocking local global labels local' global' spawned :
  seq_step local global labels local' global' spawned ->
  local.(seq_nb_state) = false.
Proof. intros Hstep. inversion Hstep. assumption. Qed.

Lemma seqStepFromNonblockingImpossible local global labels local' global' spawned :
  local.(seq_nb_state) = true ->
  ~ seq_step local global labels local' global' spawned.
Proof.
  intros Hnonblocking Hstep.
  pose proof (seqStepSourceBlocking _ _ _ _ _ _ Hstep) as Hblocking.
  congruence.
Qed.

Lemma islaInstructionTrapStopsMicroPath state observations after :
  IslaInstructionTrap state ->
  IslaMicroPath state observations after ->
  observations = [] /\ after = state.
Proof.
  intros Htrap Hpath. inversion Hpath; subst; first done.
  exfalso. eapply seqStepFromNonblockingImpossible; eauto.
Qed.

Lemma islaInstructionRunCountsOneSegment before observations after :
  IslaInstructionSegment before observations after ->
  IslaInstructionRun 1 before [observations] after.
Proof. intros Hsegment. econstructor; eauto. constructor. Qed.

Lemma islaStoppedInstructionRunCount exitState count before segments after :
  IslaStoppedInstructionRun exitState count before segments after ->
  length segments = count.
Proof. intros Hrun. induction Hrun; simpl; congruence. Qed.

Lemma islaStoppedInstructionRunAtExitIsZero exitState count before segments after :
  exitState before ->
  IslaStoppedInstructionRun exitState count before segments after ->
  count = 0%nat /\ segments = [] /\ after = before.
Proof.
  intros Hexit Hrun. inversion Hrun; subst; first auto.
  contradiction.
Qed.

Print Assumptions islaInstructionSegmentCorrespondence.
Print Assumptions islaInstructionRunCorrespondence.
Print Assumptions islaInstructionRunCount.
Print Assumptions seqStepFromNonblockingImpossible.
Print Assumptions islaInstructionTrapStopsMicroPath.
Print Assumptions islaInstructionSegmentIntro.
Print Assumptions islaStoppedInstructionRunAtExitIsZero.

Definition islaSymbolicChoiceTrace : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "choice" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  tnil.

Definition islaSymbolicChoiceAfter (choice : bv 64)
    (regs : reg_map) : seq_local_state := {|
  seq_trace :=
    ReadReg "choice" [] (RVal_Bits choice) Mk_annot :t: tnil;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition islaSymbolicChoiceBefore (regs : reg_map) : seq_local_state := {|
  seq_trace := islaSymbolicChoiceTrace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma islaSymbolicChoiceStep choice regs global :
  seq_step (islaSymbolicChoiceBefore regs) global []
    (islaSymbolicChoiceAfter choice regs) global [].
Proof.
  eapply (SeqStep _ _ None
    (ReadReg "choice" [] (RVal_Bits choice) Mk_annot :t: tnil) None).
  - reflexivity.
  - apply DeclareConstBitVecS' with (b := choice).
  - simpl. repeat split; reflexivity.
Qed.

Lemma seqStepIsNondeterministic regs global :
  exists first second,
    seq_step (islaSymbolicChoiceBefore regs) global [] first global [] /\
    seq_step (islaSymbolicChoiceBefore regs) global [] second global [] /\
    first <> second.
Proof.
  exists (islaSymbolicChoiceAfter (BV 64 0) regs).
  exists (islaSymbolicChoiceAfter (BV 64 1) regs).
  split; first apply islaSymbolicChoiceStep.
  split; first apply islaSymbolicChoiceStep.
  intros Heq. inversion Heq.
Qed.

Print Assumptions seqStepIsNondeterministic.
