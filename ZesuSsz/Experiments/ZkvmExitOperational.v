From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.
From IslaTraces.zkvm_exit Require Import instrs.

Record IslarisEndpointState : Type := {
  endpointLocal : seq_local_state;
  endpointGlobal : seq_global_state
}.

Definition islarisEndpointPc (state : IslarisEndpointState) : option Z :=
  match endpointLocal state with
  | {| seq_regs := regs; seq_pc_reg := pcReg |} =>
      match regs !! pcReg with
      | Some (RVal_Bits pc) =>
          if N.eqb (bvn_n pc) 64 then Some (bvn_unsigned pc) else None
      | _ => None
      end
  end.

(** One contract step executes exactly one generated instruction trace. *)
Definition islarisInstructionStep (_ : nat)
    (before after : IslarisEndpointState) : Prop :=
  exists (pc : bv 64) trace observations,
    seq_trace (endpointLocal before) = tnil /\
    seq_nb_state (endpointLocal before) = false /\
    seq_regs (endpointLocal before) !! seq_pc_reg (endpointLocal before) =
      Some (RVal_Bits pc) /\
    seq_instrs (endpointGlobal before) !! pc = Some trace /\
    nsteps (S (isla_trace_length trace))
      ([endpointLocal before], endpointGlobal before)
      observations
      ([endpointLocal after], endpointGlobal after) /\
    seq_trace (endpointLocal after) = tnil /\
    seq_nb_state (endpointLocal after) = false.

(** Canonical states make the operational discharge obligation executable. *)
Definition zkvmExitInstrMap : gmap (bv 64) isla_trace :=
  <[Z_to_bv 64 0x101cc := a101cc]>
  (<[Z_to_bv 64 0x101c8 := a101c8]>
  (<[Z_to_bv 64 0x101c4 := a101c4]> ∅)).

Definition zkvmExitInitialRegs (code oldX5 : bv 64) : reg_map :=
  <["satp" := RVal_Bits (Z_to_bv 64 0)]>
  (<["mstatus" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]]>
  (<["misa" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0x8000000000001100))]]>
  (<["cur_privilege" := RVal_Enum "Machine"]>
  (<["rv_htif_tohost" := RVal_Bits (Z_to_bv 64 0x40001000)]>
  (<["rv_clint_size" := RVal_Bits (Z_to_bv 64 0xc0000)]>
  (<["rv_clint_base" := RVal_Bits (Z_to_bv 64 0x2000000)]>
  (<["rv_rom_size" := RVal_Bits (Z_to_bv 64 0x100)]>
  (<["rv_rom_base" := RVal_Bits (Z_to_bv 64 0x1000)]>
  (<["rv_ram_size" := RVal_Bits (Z_to_bv 64 0x40000000)]>
  (<["rv_ram_base" := RVal_Bits (Z_to_bv 64 0)]>
  (<["rv_enable_misaligned_access" := RVal_Bool false]>
  (<["rv_enable_pmp" := RVal_Bool false]>
  (<["x10" := RVal_Bits code]>
  (<["x5" := RVal_Bits oldX5]>
  (<["PC" := RVal_Bits (Z_to_bv 64 0x101c4)]> ∅))))))))))))))).

Definition zkvmExitLocal (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition zkvmExitGlobal (mem : mem_map) : seq_global_state := {|
  seq_instrs := zkvmExitInstrMap;
  seq_mem := mem
|}.

Definition zkvmExitState (regs : reg_map) (mem : mem_map) : IslarisEndpointState := {|
  endpointLocal := zkvmExitLocal regs;
  endpointGlobal := zkvmExitGlobal mem
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
        try naive_solver eauto using frameLocalRegsLookupSome, frameLocalRegsCongruence,
          frameLocalRegsWriteAfterTrace.
    + destruct Hmatch as (-> & -> & ->). cbn. repeat split; reflexivity.
  Unshelve.
  all: first [exact (Z_to_bv _ 0) | exact (∅ : mem_map)].
Qed.

Definition zkvmExitRegsAfterAuipc (code oldX5 : bv 64) : reg_map :=
  <["PC" := RVal_Bits (Z_to_bv 64 0x101c8)]>
  (<["x5" := RVal_Bits (Z_to_bv 64 0x2401a1c4)]>
    (zkvmExitInitialRegs code oldX5)).

Definition zkvmExitRegsAfterAddi (code oldX5 : bv 64) : reg_map :=
  <["PC" := RVal_Bits ((Z_to_bv 64 0x101c8 + Z_to_bv 64 4)%bv)]>
  (<["x5" := RVal_Bits
      ((Z_to_bv 64 0x2401a1c4 + Z_to_bv 64 0xfffffffffffffef4)%bv)]>
    (zkvmExitRegsAfterAuipc code oldX5)).

Definition zkvmExitRegsAfterStore (code oldX5 : bv 64) : reg_map :=
  <["PC" := RVal_Bits
      ((Z_to_bv 64 0x101c8 + Z_to_bv 64 4 + Z_to_bv 64 4)%bv)]>
    (zkvmExitRegsAfterAddi code oldX5).

Ltac solve_pure_match :=
  cbn;
  repeat first [left | split | eexists];
  try reflexivity.

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

Ltac pure_trace_nstep :=
  eapply nsteps_l with (κ := []) (κs := []);
  [ eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [ reflexivity | reflexivity |
      eapply SeqStep with (κ' := None);
      [ reflexivity |
        first [eapply DeclareConstBitVecS' |
               econstructor; cbn; reflexivity |
               constructor] |
        solve_pure_match ] ] |
    cbn ].

Lemma zkvmExitAuipcStep code oldX5 mem :
  islarisInstructionStep 0
    (zkvmExitState (zkvmExitInitialRegs code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterAuipc code oldX5) mem).
Proof.
  unfold islarisInstructionStep.
  eexists (Z_to_bv 64 0x101c4), a101c4, [].
  repeat split; try reflexivity.
  cbn.
  eapply nsteps_l with (κ := []) (κs := []).
  - eapply step_atomic with (t1 := []) (t2 := []) (efs := []).
    + reflexivity.
    + reflexivity.
    + eapply SeqStep with (κ' := None).
      * reflexivity.
      * constructor.
      * cbn.
        split; first reflexivity.
        eexists (Z_to_bv 64 0x101c4).
        split; first reflexivity.
        cbn. repeat split; reflexivity.
  - cbn.
    repeat pure_trace_nstep.
    constructor.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma zkvmExitAddiStep code oldX5 mem :
  islarisInstructionStep 1
    (zkvmExitState (zkvmExitRegsAfterAuipc code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterAddi code oldX5) mem).
Proof.
  unfold islarisInstructionStep.
  eexists (Z_to_bv 64 0x101c8), a101c8, [].
  repeat split; try reflexivity.
  cbn.
  eapply nsteps_l with (κ := []) (κs := []).
  - eapply step_atomic with (t1 := []) (t2 := []) (efs := []).
    + reflexivity.
    + reflexivity.
    + eapply SeqStep with (κ' := None).
      * reflexivity.
      * constructor.
      * cbn.
        split; first reflexivity.
        eexists (Z_to_bv 64 0x101c8).
        split; first reflexivity.
        cbn. repeat split; reflexivity.
  - cbn.
    repeat pure_trace_nstep.
    constructor.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma zkvmExitStoreStep code oldX5 mem oldExitCode :
  read_mem mem 0x2401a0d0 8 = Some oldExitCode ->
  islarisInstructionStep 2
    (zkvmExitState (zkvmExitRegsAfterAddi code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterStore code oldX5)
      (write_mem 8 mem (Z_to_bv 64 0x2401a0d0) (bv_unsigned code))).
Proof.
  intros Hmem.
  unfold islarisInstructionStep.
  eexists (Z_to_bv 64 0x101cc), a101cc, [].
  repeat split; try reflexivity.
  cbn.
  eapply nsteps_l with (κ := []) (κs := []).
  - eapply step_atomic with (t1 := []) (t2 := []) (efs := []).
    + reflexivity.
    + reflexivity.
    + eapply SeqStep with (κ' := None).
      * reflexivity.
      * constructor.
      * cbn.
        split; first reflexivity.
        eexists (Z_to_bv 64 0x101cc).
        split.
        -- cbn. f_equal.
        -- cbn. repeat split; reflexivity.
  - cbn.
    repeat pure_trace_nstep.
    all: try apply readAccessorZToBv.
    + replace
        ((Z_to_bv 64 0x2401a1c4 +
          Z_to_bv 64 0xfffffffffffffef4 + 24)%bv)
        with (Z_to_bv 64 0x2401a0d0) by bv_solve.
      replace (bv_unsigned (Z_to_bv 64 0x2401a0d0))
        with 0x2401a0d0 by bv_solve.
      rewrite Hmem.
      repeat split; reflexivity.
    + pure_trace_nstep. constructor.
  Unshelve. all: try exact (Z_to_bv 64 0); try exact false.
Qed.

Definition zkvmExitCanonicalEntry (args : ZkvmExitArgs)
    (state : IslarisEndpointState) : Prop :=
  0 <= zkvmExitCode args < 2 ^ 64 /\
  exists (oldX5 : bv 64) mem oldExitCode,
    read_mem mem 0x2401a0d0 8 = Some oldExitCode /\
    state = zkvmExitState
      (zkvmExitInitialRegs (Z_to_bv 64 (zkvmExitCode args)) oldX5) mem.

Definition zkvmExitCanonicalPost (args : ZkvmExitArgs) (_ : unit)
    (before after : IslarisEndpointState) : Prop :=
  exists (oldX5 : bv 64) mem oldExitCode,
    read_mem mem 0x2401a0d0 8 = Some oldExitCode /\
    before = zkvmExitState
      (zkvmExitInitialRegs (Z_to_bv 64 (zkvmExitCode args)) oldX5) mem /\
    after = zkvmExitState
      (zkvmExitRegsAfterStore (Z_to_bv 64 (zkvmExitCode args)) oldX5)
      (write_mem 8 mem (Z_to_bv 64 0x2401a0d0)
        (bv_unsigned (Z_to_bv 64 (zkvmExitCode args)))).

Definition zkvmExitCanonicalModel :
    Level1MachineModel IslarisEndpointState unit := {|
  endpointStep := islarisInstructionStep;
  endpointPc := islarisEndpointPc;
  readInputEntry := fun _ _ => False;
  readInputExit := fun _ _ _ _ => False;
  allocatorGetEntry := fun _ _ => False;
  allocatorGetExit := fun _ _ _ _ => False;
  decodeBoundaryEntry := fun _ _ => False;
  decodeBoundaryExit := fun _ _ _ _ => False;
  writeSuccessEntry := fun _ _ => False;
  writeSuccessExit := fun _ _ _ _ => False;
  writeFailureEntry := fun _ _ => False;
  writeFailureExit := fun _ _ _ _ => False;
  zkvmExitEntry := zkvmExitCanonicalEntry;
  zkvmExitPost := zkvmExitCanonicalPost;
  referenceDecodes := fun _ _ => False;
  decodedResultRelModuloKnownBugs := fun _ _ _ => False;
  avoidsReviewedDomainDivergences := fun _ _ => False;
  knownBugApplies := fun _ _ _ => False;
  decodeObservationSuccess := fun _ _ => False;
  decodeObservationFailure := fun _ => False
|}.

Lemma zkvmExitCanonicalImplements :
  Implements zkvmExitCanonicalModel ZkvmExitExecutionPc
    (PcInList zkvmExitExitPcs)
    (zkvmExitContract zkvmExitCanonicalModel (fun _ => 3%nat)).
Proof.
  unfold Implements, ContractImplements.
  intros [code] fromStep before
    (Hcode & oldX5 & mem & oldExitCode & Hmem & ->).
  eexists 3%nat,
    (zkvmExitState
      (zkvmExitRegsAfterStore (Z_to_bv 64 code) oldX5)
      (write_mem 8 mem (Z_to_bv 64 0x2401a0d0)
        (bv_unsigned (Z_to_bv 64 code)))), tt.
  repeat split.
  - cbn. lia.
  - cbn. lia.
  - eapply ConfinedTraceStep with
      (address := 0x101c4)
      (middle := zkvmExitState
        (zkvmExitRegsAfterAuipc (Z_to_bv 64 code) oldX5) mem).
    + reflexivity.
    + unfold ZkvmExitExecutionPc, PcInRanges. split.
      * eexists 0x101c4, 0x101d4. split.
        -- cbn. left. reflexivity.
        -- lia.
      * unfold zkvmExitTerminalPc. lia.
    + apply zkvmExitAuipcStep.
    + eapply ConfinedTraceStep with
        (address := 0x101c8)
        (middle := zkvmExitState
          (zkvmExitRegsAfterAddi (Z_to_bv 64 code) oldX5) mem).
      * cbn. f_equal.
      * unfold ZkvmExitExecutionPc, PcInRanges. split.
        -- eexists 0x101c4, 0x101d4. split.
           ++ cbn. left. reflexivity.
           ++ lia.
        -- unfold zkvmExitTerminalPc. lia.
      * apply zkvmExitAddiStep.
      * eapply ConfinedTraceStep with
          (address := 0x101cc)
          (middle := zkvmExitState
            (zkvmExitRegsAfterStore (Z_to_bv 64 code) oldX5)
            (write_mem 8 mem (Z_to_bv 64 0x2401a0d0)
              (bv_unsigned (Z_to_bv 64 code)))).
        -- cbn. f_equal.
        -- unfold ZkvmExitExecutionPc, PcInRanges. split.
           ++ eexists 0x101c4, 0x101d4. split.
              ** cbn. left. reflexivity.
              ** lia.
           ++ unfold zkvmExitTerminalPc. lia.
        -- eapply zkvmExitStoreStep. exact Hmem.
        -- constructor.
  - eexists 0x101d0. split.
    + cbn. f_equal.
    + cbn. left. reflexivity.
  - eexists oldX5, mem, oldExitCode. split; first exact Hmem.
    split; reflexivity.
Qed.

Theorem level1ZkvmExitCanonical :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    Implements zkvmExitCanonicalModel ZkvmExitExecutionPc
      (PcInList zkvmExitExitPcs)
      (zkvmExitContract zkvmExitCanonicalModel (fun _ => bound)).
Proof.
  eexists 3%nat. split.
  - unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound.
    lia.
  - exact zkvmExitCanonicalImplements.
Qed.
