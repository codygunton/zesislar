From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuSsz.Experiments.OperationalBridge.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.

(** The production I/O context is below the tutorial RAM window. This register
    collection matches the focused trace-generation configuration. *)
Definition zesu_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x0)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x40000000)));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 0x1000)));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 0x100)));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 0x2000000)));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 0xc0000)));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x40001000)));
  (KindReg "cur_privilege", ExactShape (RVal_Enum "Machine"));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0x8000000000001100))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].

Lemma zkvm_exit_instruction_body `{!islaG Σ} `{!threadG}
    (code old_x5 old_exit_code : bv 64) :
  instr 0x101c4 (Some a101c4) -∗
  instr 0x101c8 (Some a101c8) -∗
  instr 0x101cc (Some a101cc) -∗
  instr_body 0x101c4 (
    reg_col zesu_sys_regs ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits code ∗
    0x2401a0d0 ↦ₘ old_exit_code ∗
    instr_pre 0x101d0 (
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      0x2401a0d0 ↦ₘ code ∗
      True)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: liShow.
  all: try bv_solve.
Qed.

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

Definition zkvmExitState := operationalState zkvmExitInstrMap.

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

Lemma zkvmExitAuipcStep code oldX5 mem :
  operationalInstructionStep 0
    (zkvmExitState (zkvmExitInitialRegs code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterAuipc code oldX5) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x101c4) a101c4.
  repeat operational_trace_step.
  constructor.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma zkvmExitAddiStep code oldX5 mem :
  operationalInstructionStep 1
    (zkvmExitState (zkvmExitRegsAfterAuipc code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterAddi code oldX5) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x101c8) a101c8.
  repeat operational_trace_step.
  constructor.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma zkvmExitStoreStep code oldX5 mem oldExitCode :
  read_mem mem 0x2401a0d0 8 = Some oldExitCode ->
  operationalInstructionStep 2
    (zkvmExitState (zkvmExitRegsAfterAddi code oldX5) mem)
    (zkvmExitState (zkvmExitRegsAfterStore code oldX5)
      (write_mem 8 mem (Z_to_bv 64 0x2401a0d0) (bv_unsigned code))).
Proof.
  intros Hmem.
  operational_begin_instruction (Z_to_bv 64 0x101cc) a101cc.
  repeat operational_trace_step.
  all: try apply readAccessorZToBv.
  - replace
      ((Z_to_bv 64 0x2401a1c4 +
        Z_to_bv 64 0xfffffffffffffef4 + 24)%bv)
      with (Z_to_bv 64 0x2401a0d0) by bv_solve.
    replace (bv_unsigned (Z_to_bv 64 0x2401a0d0))
      with 0x2401a0d0 by bv_solve.
    rewrite Hmem.
    repeat split; reflexivity.
  - operational_trace_step. constructor.
  Unshelve. all: try exact (Z_to_bv 64 0); try exact false.
Qed.

Definition zkvmExitCanonicalEntry (args : ZkvmExitArgs)
    (state : OperationalState) : Prop :=
  0 <= zkvmExitCode args < 2 ^ 64 /\
  exists (oldX5 : bv 64) mem oldExitCode,
    read_mem mem 0x2401a0d0 8 = Some oldExitCode /\
    state = zkvmExitState
      (zkvmExitInitialRegs (Z_to_bv 64 (zkvmExitCode args)) oldX5) mem.

Definition zkvmExitCanonicalPost (args : ZkvmExitArgs) (_ : unit)
    (before after : OperationalState) : Prop :=
  exists (oldX5 : bv 64) mem oldExitCode,
    read_mem mem 0x2401a0d0 8 = Some oldExitCode /\
    before = zkvmExitState
      (zkvmExitInitialRegs (Z_to_bv 64 (zkvmExitCode args)) oldX5) mem /\
    after = zkvmExitState
      (zkvmExitRegsAfterStore (Z_to_bv 64 (zkvmExitCode args)) oldX5)
      (write_mem 8 mem (Z_to_bv 64 0x2401a0d0)
        (bv_unsigned (Z_to_bv 64 (zkvmExitCode args)))).

Definition zkvmExitCanonicalModel :
    Level1MachineModel OperationalState unit := {|
  endpointStep := operationalInstructionStep;
  endpointPc := operationalPc;
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
