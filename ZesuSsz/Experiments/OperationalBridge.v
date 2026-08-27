From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.

Record OperationalState : Type := {
  operationalLocal : seq_local_state;
  operationalGlobal : seq_global_state
}.

Definition operationalPc (state : OperationalState) : option Z :=
  match operationalLocal state with
  | {| seq_regs := regs; seq_pc_reg := pcReg |} =>
      match regs !! pcReg with
      | Some (RVal_Bits pc) =>
          if N.eqb (bvn_n pc) 64 then Some (bvn_unsigned pc) else None
      | _ => None
      end
  end.

(** One contract step executes one instruction trace from [tnil] to [tnil]. *)
Definition operationalInstructionStep (_ : nat)
    (before after : OperationalState) : Prop :=
  exists (pc : bv 64) trace observations,
    seq_trace (operationalLocal before) = tnil /\
    seq_nb_state (operationalLocal before) = false /\
    seq_regs (operationalLocal before) !!
      seq_pc_reg (operationalLocal before) = Some (RVal_Bits pc) /\
    seq_instrs (operationalGlobal before) !! pc = Some trace /\
    nsteps (S (isla_trace_length trace))
      ([operationalLocal before], operationalGlobal before)
      observations
      ([operationalLocal after], operationalGlobal after) /\
    seq_trace (operationalLocal after) = tnil /\
    seq_nb_state (operationalLocal after) = false.

Definition operationalLocalState (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition operationalGlobalState
    (instructions : gmap (bv 64) isla_trace) (memory : mem_map) :
    seq_global_state := {|
  seq_instrs := instructions;
  seq_mem := memory
|}.

Definition operationalState (instructions : gmap (bv 64) isla_trace)
    (regs : reg_map) (memory : mem_map) : OperationalState := {|
  operationalLocal := operationalLocalState regs;
  operationalGlobal := operationalGlobalState instructions memory
|}.

(** Add registers without changing any register already present in [local]. *)
Definition frameLocalRegs (extra : reg_map)
    (local : seq_local_state) : seq_local_state :=
  local <| seq_regs := seq_regs local ∪ extra |>.

Lemma frameLocalRegsLookup extra local register :
  seq_regs (frameLocalRegs extra local) !! register =
    (seq_regs local ∪ extra) !! register.
Proof. reflexivity. Qed.

Lemma frameLocalRegsLookupSome extra local register value :
  seq_regs local !! register = Some value ->
  seq_regs (frameLocalRegs extra local) !! register = Some value.
Proof.
  rewrite frameLocalRegsLookup.
  apply lookup_union_Some_l.
Qed.

Lemma frameLocalRegsTrace extra local trace :
  frameLocalRegs extra (local <| seq_trace := trace |>) =
    frameLocalRegs extra local <| seq_trace := trace |>.
Proof. reflexivity. Qed.

Lemma frameLocalRegsBlocking extra local blocking :
  frameLocalRegs extra (local <| seq_nb_state := blocking |>) =
    frameLocalRegs extra local <| seq_nb_state := blocking |>.
Proof. reflexivity. Qed.

Lemma frameLocalRegsCongruence extra (left right : seq_local_state) :
  left = right -> frameLocalRegs extra left = frameLocalRegs extra right.
Proof. intros ->. reflexivity. Qed.

Lemma frameLocalRegsWrite extra local trace
    (register : sail_name) (value : valu) :
  frameLocalRegs extra
      (local <| seq_trace := trace |>
        <| seq_regs := <[register := value]> (seq_regs local) |>) =
    frameLocalRegs extra local
      <| seq_trace := trace |>
      <| seq_regs := <[register := value]>
          (seq_regs (frameLocalRegs extra local)) |>.
Proof.
  cbn [frameLocalRegs]. rewrite insert_union_l. reflexivity.
Qed.

Lemma frameLocalRegsWriteAfterTrace extra local trace
    (register : sail_name) (value : valu) :
  frameLocalRegs extra
      (local <| seq_trace := trace |>
        <| seq_regs := <[register := value]> (seq_regs local) |>) =
    frameLocalRegs extra (local <| seq_trace := trace |>)
      <| seq_regs := <[register := value]>
          (seq_regs (frameLocalRegs extra local)) |>.
Proof.
  cbn [frameLocalRegs]. rewrite insert_union_l. reflexivity.
Qed.

(** A trace is frame-compatible when added registers do not change its next event. *)
Definition traceStepFrameCompatible (trace : isla_trace)
    (regs extra : reg_map) : Prop :=
  forall label next,
    trace_step trace regs label next ->
    trace_step trace (regs ∪ extra) label next.

Lemma seqStepFrame extra local global labels local' global' spawned :
  seq_step local global labels local' global' spawned ->
  traceStepFrameCompatible
    (seq_trace local) (seq_regs local) extra ->
  seq_step (frameLocalRegs extra local) global labels
    (frameLocalRegs extra local') global'
    (frameLocalRegs extra <$> spawned).
Proof.
  intros Hstep Hcompatible.
  destruct Hstep as [global local internal next internal' local' global'
    Hblocking Htrace Hmatch].
  econstructor.
  - exact Hblocking.
  - apply Hcompatible. exact Htrace.
  - destruct internal as [label |]; cbn in *.
    + destruct label; cbn in Hmatch |-;
        rewrite ?insert_union_l;
        rewrite <- ?frameLocalRegsTrace, <- ?frameLocalRegsBlocking,
          <- ?frameLocalRegsWrite, <- ?frameLocalRegsWriteAfterTrace;
        repeat match goal with
        | H : ex _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : _ \/ _ |- _ => destruct H
        end;
        repeat match goal with
        | H : context [match read_mem ?memory ?address ?length with
                       | Some _ => _ | None => _ end] |- _ =>
            destruct (read_mem memory address length) eqn:? in H
        | H : context [match ?instructions !! ?pc with
                       | Some _ => _ | None => _ end] |- _ =>
            destruct (instructions !! pc) eqn:? in H
        end;
        try cbn in Hmatch;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        | H : _ \/ _ |- _ => destruct H
        end;
        subst;
        repeat eexists;
        repeat match goal with
        | |- context [match read_mem ?memory ?address ?length with
                      | Some _ => _ | None => _ end] =>
            destruct (read_mem memory address length) eqn:?
        | |- context [match ?instructions !! ?pc with
                      | Some _ => _ | None => _ end] =>
            destruct (instructions !! pc) eqn:?
        end;
        subst;
        cbn;
        try (eapply frameLocalRegsLookupSome; eassumption);
        try apply frameLocalRegsWriteAfterTrace;
        try naive_solver eauto using frameLocalRegsLookupSome,
          frameLocalRegsCongruence, frameLocalRegsWriteAfterTrace.
    + destruct Hmatch as (-> & -> & ->). cbn. repeat split; reflexivity.
  Unshelve.
  all: first [exact (Z_to_bv _ 0) | exact (∅ : mem_map)].
Qed.

Lemma readAccessorZToBv n z `{!BvWf n z} :
  read_accessor [] (RVal_Bits (Z_to_bv n z)) =
    Some (RVal_Bits (BV n z)).
Proof.
  cbn. f_equal. f_equal. f_equal.
  apply bvn_eq. split; first reflexivity.
  unfold bvn_unsigned. cbn.
  rewrite Z_to_bv_unsigned bv_unsigned_BV.
  apply bv_wrap_small. apply bv_wf_in_range. exact BvWf0.
Qed.

Lemma bvExtractLowThreeZero (value : bv 64) :
  bv_unsigned value `mod` 8 = 0 -> bv_extract 0 3 value = 0%bv.
Proof.
  intros Haligned. apply bv_eq.
  rewrite bv_extract_0_unsigned.
  unfold bv_wrap. cbn. exact Haligned.
Qed.

Ltac operational_pure_match :=
  cbn;
  repeat first [left | split | eexists];
  try reflexivity.

Lemma nstepsSeqStep n local global local' global' final :
  seq_step local global [] local' global' [] ->
  nsteps n ([local'], global') [] final ->
  nsteps (S n) ([local], global) [] final.
Proof.
  intros Hstep Hsteps.
  eapply nsteps_l with
    (ρ2 := ([local'], global')) (κ := []) (κs := []).
  - eapply step_atomic with (t1 := []) (t2 := []) (efs := []).
    + reflexivity.
    + reflexivity.
    + exact Hstep.
  - exact Hsteps.
Qed.

Ltac operational_trace_step_visible :=
  eapply nstepsSeqStep;
  [ eapply SeqStep with (κ' := None);
    [ reflexivity |
      first [eapply DeclareConstBitVecS' |
             econstructor; cbn; reflexivity |
             constructor] |
      operational_pure_match ] |
    cbn ].

Ltac operational_trace_step :=
  eapply nsteps_l with (κ := []) (κs := []);
  [ eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [ reflexivity | reflexivity |
      eapply SeqStep with (κ' := None);
      [ reflexivity |
        first [eapply DeclareConstBitVecS' |
               econstructor; cbn; reflexivity |
               constructor] |
        operational_pure_match ] ] |
    cbn ].

(** Start one instruction and leave only its trace events as proof goals. *)
Ltac operational_begin_instruction pc trace :=
  unfold operationalInstructionStep;
  eexists pc, trace, [];
  repeat split; try reflexivity; try assumption;
  cbn;
  eapply nsteps_l with (κ := []) (κs := []);
  [ eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [ reflexivity | reflexivity |
      eapply SeqStep with (κ' := None);
      [ reflexivity | constructor |
        cbn; split; [reflexivity|];
        eexists pc; split; [first [reflexivity | assumption]|];
        cbn; repeat split; reflexivity ] ] |
    cbn ].
