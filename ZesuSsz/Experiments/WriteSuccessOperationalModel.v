From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import stdpp.base.
Require Import isla.opsem.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
From IslaTraces.write_success_00 Require Import a14d30.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Generated.WriteSuccessCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.

Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Termination, confinement, and the instruction bound quantify over
    completed-instruction executions. These are sequences of
    [IslaInstructionSegment] steps built only from unchanged [seq_step]
    transitions. One segment runs from an instruction boundary
    ([seq_nb_state = false], PC in the instruction table, trace loaded)
    through the next [LDone] step, or ends in an instruction trap.
    Raw micro-executions that end in Islaris's early nonblocking outcome
    ([seq_nb_state = true] before [LDone]) are Islaris values. They model
    abandoned trace branches. The termination claim excludes them. The
    claim does not state that every raw micro-execution reaches [0x14d10]. *)

Definition WriteSuccessRecord : Type := (seq_label * mem_map)%type.

Definition WriteSuccessConcreteState : Type :=
  (IslaState * list WriteSuccessRecord)%type.

Definition writeSuccessConcreteRegister64
    (registers : reg_map) (name : string) : Prop :=
  exists value : bv 64, registers !! name = Some (RVal_Bits value).

Definition writeSuccessConcreteOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7";
   "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessConcreteAbiRegisters : list string :=
  ["x1"; "x2"; "x8"; "x9"; "x10"; "x11"; "x12";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24";
   "x25"; "x26"; "x27"] ++ writeSuccessConcreteOtherRegisters.

Definition writeSuccessConcreteInitialState
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : IslaState) : Prop :=
  state.1.(seq_trace) = a14d30 /\
  state.1.(seq_pc_reg) = "PC" /\
  state.1.(seq_nb_state) = false /\
  state.2.(seq_instrs) !! Z_to_bv 64 0x14d30 = Some a14d30 /\
  (forall fromPc toPc,
    In (fromPc, toPc) writeSuccessGeneratedControlFlow ->
    exists trace,
      state.2.(seq_instrs) !! Z_to_bv 64 fromPc = Some trace) /\
  state.1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14d30)) /\
  state.1.(seq_regs) !! "x1" = Some
    (RVal_Bits (Z_to_bv 64
      (successReturnAddress WriteSuccessObservation args))) /\
  state.1.(seq_regs) !! "x2" = Some
    (RVal_Bits (Z_to_bv 64
      (successStackPointer WriteSuccessObservation args))) /\
  state.1.(seq_regs) !! "x10" = Some
    (RVal_Bits (Z_to_bv 64
      (successDecodedAddress WriteSuccessObservation args))) /\
  Forall (writeSuccessConcreteRegister64 state.1.(seq_regs))
    writeSuccessConcreteAbiRegisters /\
  Forall (fun item =>
      match item.1 with
      | KindReg name => exists value,
          state.1.(seq_regs) !! name = Some value /\
          valu_has_shape value item.2
      | KindField _ _ => False
      end) zesu_ram_sys_regs /\
  successReturnAddress WriteSuccessObservation args = 0x14d10 /\
  successStackPointer WriteSuccessObservation args `mod` 16 = 0 /\
  (0x20000880 <= successStackPointer WriteSuccessObservation args)%Z /\
  (successStackPointer WriteSuccessObservation args + 0x7d0 < 0x40000000)%Z /\
  (exists stackBytes,
    length stackBytes = 1896%nat /\
    read_mem_list state.2.(seq_mem)
      (successStackPointer WriteSuccessObservation args - 0x7d0) 1896%N =
      Some stackBytes) /\
  set_Forall (fun address =>
    (0x20000000 <= bv_unsigned address < 0x40000000)%Z)
    (dom state.2.(seq_mem)) /\
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.2.(seq_mem)).

Fixpoint segmentRecordsFrom (memory : mem_map)
    (observations : list IslaMicroObservation) : list WriteSuccessRecord :=
  match observations with
  | [] => []
  | observation :: rest =>
      map (fun label => (label, memory)) observation.(microLabels) ++
      segmentRecordsFrom observation.(microAfter).2.(seq_mem) rest
  end.

Definition segmentRecords (before : IslaState)
    (observations : list IslaMicroObservation) : list WriteSuccessRecord :=
  segmentRecordsFrom before.2.(seq_mem) observations.

Fixpoint flattenMicroLabels
    (observations : list IslaMicroObservation) : list seq_label :=
  match observations with
  | [] => []
  | observation :: rest =>
      observation.(microLabels) ++ flattenMicroLabels rest
  end.

Definition writeSuccessConcreteStep (_ : nat)
    (s s' : WriteSuccessConcreteState) : Prop :=
  exists observations,
    IslaInstructionSegment s.1 observations s'.1 /\
    s'.2 = s.2 ++ segmentRecords s.1 observations.

Definition writeSuccessConcretePc
    (s : WriteSuccessConcreteState) : option Z :=
  match s.1.1.(seq_regs) !! s.1.1.(seq_pc_reg) with
  | Some (RVal_Bits value) => Some (bvn_unsigned value)
  | _ => None
  end.

Definition writeSuccessConcreteEntry
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : Prop :=
  state.2 = [] /\
  writeSuccessConcretePc state = Some 0x14d30 /\
  writeSuccessConcreteInitialState args state.1 /\
  writeSuccessConcreteRepresentationOff
    (successStackPointer WriteSuccessObservation args)
    (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args).

Fixpoint writeSuccessRecordedPayloads
    (log : list WriteSuccessRecord) : option (list (list (bv 8))) :=
  match log with
  | [] => Some []
  | (SWriteMem pointerPort data, memory) ::
      (SWriteMem sizePort size, _) :: rest =>
      if bool_decide
          (bv_unsigned pointerPort = 0x2401a0c0 /\
           bv_unsigned sizePort = 0x2401a0c8) then
        match read_mem_list memory (bvn_unsigned data)
            (Z.to_N (bvn_unsigned size)),
          writeSuccessRecordedPayloads rest with
        | Some payload, Some payloads => Some (payload :: payloads)
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition writeSuccessObservedBytes
    (log : list WriteSuccessRecord) : option ByteString :=
  match writeSuccessRecordedPayloads log with
  | Some payloads => Some (writeSuccessPublicBytes (concat payloads))
  | None => None
  end.

Definition writeSuccessPreservedState
    (args : WriteSuccessArgs WriteSuccessObservation)
    (s s' : WriteSuccessConcreteState) : Prop :=
  let regs := s.1.1.(seq_regs) in
  let regs' := s'.1.1.(seq_regs) in
  let sp := successStackPointer WriteSuccessObservation args in
  regs' !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14d10)) /\
  regs' !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x14d10)) /\
  regs' !! "x2" = regs !! "x2" /\
  Forall (fun register => regs' !! register = regs !! register)
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23";
     "x24"; "x25"; "x26"; "x27"] /\
  Forall (fun item =>
    match item.1 with
    | KindReg register => regs' !! register = regs !! register
    | KindField _ _ => True
    end) zesu_ram_sys_regs /\
  s'.1.1.(seq_pc_reg) = "PC" /\
  s'.1.1.(seq_nb_state) = false /\
  s'.1.2.(seq_instrs) = s.1.2.(seq_instrs) /\
  dom s'.1.2.(seq_mem) = dom s.1.2.(seq_mem) /\
  (forall address : bv 64,
    ~ (writeSuccessCalleeStackLow sp <= bv_unsigned address < sp) ->
    s'.1.2.(seq_mem) !! address = s.1.2.(seq_mem) !! address).

Lemma writeSuccessConcreteEntryLogEmpty args state :
  writeSuccessConcreteEntry args state -> state.2 = [].
Proof. intros (Hlog & _). exact Hlog. Qed.

Lemma writeSuccessConcreteEntryPc args state :
  writeSuccessConcreteEntry args state ->
  writeSuccessConcretePc state = Some 0x14d30.
Proof. intros (_ & Hpc & _). exact Hpc. Qed.

Lemma writeSuccessConcreteEntryDomInRam args state :
  writeSuccessConcreteEntry args state ->
  set_Forall (fun address =>
    (0x20000000 <= bv_unsigned address < 0x40000000)%Z)
    (dom state.1.2.(seq_mem)).
Proof.
  intros (_ & _ & Hinitial & _).
  unfold writeSuccessConcreteInitialState in Hinitial.
  tauto.
Qed.

Lemma writeSuccessConcreteEntryBlocking args state :
  writeSuccessConcreteEntry args state ->
  state.1.1.(seq_nb_state) = false.
Proof.
  intros (_ & _ & Hinitial & _).
  unfold writeSuccessConcreteInitialState in Hinitial.
  tauto.
Qed.

Lemma writeSuccessConcreteEntryRejectsNonblocking args state :
  state.1.1.(seq_nb_state) = true ->
  ~ writeSuccessConcreteEntry args state.
Proof.
  intros Hnonblocking Hentry.
  pose proof (writeSuccessConcreteEntryBlocking _ _ Hentry) as Hblocking.
  rewrite Hnonblocking in Hblocking. discriminate.
Qed.

Lemma segmentRecordsFrom_app before first middle second :
  IslaMicroPath before first middle ->
  segmentRecordsFrom before.2.(seq_mem) (first ++ second) =
    segmentRecordsFrom before.2.(seq_mem) first ++
      segmentRecordsFrom middle.2.(seq_mem) second.
Proof.
  intros Hfirst. induction Hfirst; simpl; first reflexivity.
  rewrite IHHfirst app_assoc. reflexivity.
Qed.

Lemma segmentRecords_app before first middle second :
  IslaMicroPath before first middle ->
  segmentRecords before (first ++ second) =
    segmentRecords before first ++ segmentRecords middle second.
Proof. apply segmentRecordsFrom_app. Qed.

Lemma segmentRecordsLabels before observations :
  map fst (segmentRecords before observations) =
    flattenMicroLabels observations.
Proof.
  unfold segmentRecords. revert before.
  induction observations as [|observation rest IH]; intros before;
    simpl; first reflexivity.
  rewrite map_app map_map IH. f_equal.
  change (map (fun label : seq_label => label)
    observation.(microLabels) = observation.(microLabels)).
  apply map_id.
Qed.

Lemma writeSuccessConcreteStepProjection index before after :
  writeSuccessConcreteStep index before after ->
  exists observations,
    IslaInstructionSegment before.1 observations after.1.
Proof. intros (observations & Hsegment & _). eauto. Qed.

Lemma writeSuccessConcreteStepRecords index before after :
  writeSuccessConcreteStep index before after ->
  exists observations,
    IslaInstructionSegment before.1 observations after.1 /\
    after.2 = before.2 ++ segmentRecords before.1 observations.
Proof. exact (fun Hstep => Hstep). Qed.

Lemma writeSuccessStoppedTraceRun exitPc fromStep count before after :
  StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc exitPc
    fromStep count before after ->
  exists segments,
    IslaInstructionRun count before.1 segments after.1 /\
    after.2 = before.2 ++
      segmentRecords before.1 (flattenMicroObservations segments).
Proof.
  intros Htrace. induction Htrace as
    [fromStep state |
     fromStep count before middle after HnotExit Hstep Htrace IH].
  - exists []. split.
    + exact (IslaInstructionRunZero state.1).
    + cbn. rewrite app_nil_r. reflexivity.
  - destruct Hstep as (observations & Hsegment & HmiddleLog).
    destruct IH as (segments & Hrun & HafterLog).
    exists (observations :: segments). split.
    + econstructor; eassumption.
    + simpl.
      rewrite HafterLog HmiddleLog.
      rewrite (segmentRecords_app before.1 observations middle.1
        (flattenMicroObservations segments)).
      * rewrite app_assoc. reflexivity.
      * exact (islaInstructionSegmentCorrespondence _ _ _ Hsegment).
Qed.

Lemma writeSuccessRecordedPayloads_app first second firstPayloads secondPayloads :
  writeSuccessRecordedPayloads first = Some firstPayloads ->
  writeSuccessRecordedPayloads second = Some secondPayloads ->
  writeSuccessRecordedPayloads (first ++ second) =
    Some (firstPayloads ++ secondPayloads).
Proof.
  assert (Happ : forall (bound : nat) (first : list WriteSuccessRecord)
      (firstPayloads : list (list (bv 8))),
    length first <= bound ->
    writeSuccessRecordedPayloads first = Some firstPayloads ->
    writeSuccessRecordedPayloads second = Some secondPayloads ->
    writeSuccessRecordedPayloads (first ++ second) =
      Some (firstPayloads ++ secondPayloads)).
  { induction bound as [|bound IH];
      intros first' payloads Hlength Hfirst Hsecond.
    - destruct first'; last (simpl in Hlength; lia).
      simpl in Hfirst |- *. inversion Hfirst. subst. exact Hsecond.
    - destruct first' as
        [|[[firstAddress firstValue|firstAddress firstValue|firstAddress]
             firstMemory] tail]; simpl in Hfirst |- *.
      + inversion Hfirst. subst. exact Hsecond.
      + discriminate Hfirst.
      + destruct tail as
          [|[[secondAddress secondValue|secondAddress secondValue|secondAddress]
               secondMemory] rest]; try discriminate Hfirst.
        destruct (bool_decide
          (bv_unsigned firstAddress = 0x2401a0c0 /\
           bv_unsigned secondAddress = 0x2401a0c8)) eqn:Hports;
          try discriminate Hfirst.
        destruct (read_mem_list firstMemory (bvn_unsigned firstValue)
          (Z.to_N (bvn_unsigned secondValue))) as [payload|] eqn:Hread;
          try discriminate Hfirst.
        destruct (writeSuccessRecordedPayloads rest) as [restPayloads|]
          eqn:Hrest; try discriminate Hfirst.
        inversion Hfirst. subst payloads.
        have HlengthRest : length rest <= bound by (simpl in Hlength; lia).
        specialize (IH rest restPayloads HlengthRest Hrest Hsecond).
        cbn.
        rewrite Hports Hread IH. reflexivity.
      + discriminate Hfirst.
  }
  eapply Happ with (bound := length first); try eassumption.
  reflexivity.
Qed.

Print Assumptions segmentRecords_app.
Print Assumptions segmentRecordsLabels.
Print Assumptions writeSuccessConcreteEntryLogEmpty.
Print Assumptions writeSuccessConcreteEntryPc.
Print Assumptions writeSuccessConcreteEntryDomInRam.
Print Assumptions writeSuccessConcreteEntryBlocking.
Print Assumptions writeSuccessConcreteEntryRejectsNonblocking.
Print Assumptions writeSuccessConcreteStepProjection.
Print Assumptions writeSuccessConcreteStepRecords.
Print Assumptions writeSuccessStoppedTraceRun.
Print Assumptions writeSuccessRecordedPayloads_app.
