Require Import isla.riscv64.riscv64.
From IslaTraces.allocator_get Require Import instrs.
Require Import ZesuSsz.Experiments.OperationalBridge.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.

Definition allocator_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x20000000)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x20000000)));
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

Lemma allocator_get_instruction_body `{!islaG Σ} `{!threadG}
    (sp old_x10 old_x11 old_x12 old_x13 stack0 stack8 : bv 64) :
  instr 0x14ccc (Some a14ccc) -∗
  instr 0x14cd0 (Some a14cd0) -∗
  instr 0x14cd4 (Some a14cd4) -∗
  instr 0x14cd8 (Some a14cd8) -∗
  instr 0x14cdc (Some a14cdc) -∗
  instr 0x14ce0 (Some a14ce0) -∗
  instr 0x14ce4 (Some a14ce4) -∗
  instr 0x14ce8 (Some a14ce8) -∗
  instr_body 0x14ccc (
    reg_col allocator_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits old_x10 ∗
    "x11" ↦ᵣ RVal_Bits old_x11 ∗
    "x12" ↦ᵣ RVal_Bits old_x12 ∗
    "x13" ↦ᵣ RVal_Bits old_x13 ∗
    bv_unsigned sp ↦ₘ stack0 ∗
    (bv_unsigned sp + 8) ↦ₘ stack8 ∗
    (bv_unsigned sp + 16) ↦ₘ? 8 ∗
    (bv_unsigned sp + 24) ↦ₘ? 8 ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(0x20000000 ≤ bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 24 < 0x40000000)%Z⌝ ∗
    instr_pre 0x14cec (
      reg_col allocator_sys_regs ∗
      "x2" ↦ᵣ RVal_Bits sp ∗
      "x10" ↦ᵣ RVal_Bits (BV 64 0x2401a0b0) ∗
      "x11" ↦ᵣ RVal_Bits (BV 64 0x177a8) ∗
      "x12" ↦ᵣ RVal_Bits stack0 ∗
      "x13" ↦ᵣ RVal_Bits stack8 ∗
      bv_unsigned sp ↦ₘ stack0 ∗
      (bv_unsigned sp + 8) ↦ₘ stack8 ∗
      (bv_unsigned sp + 16) ↦ₘ (BV 64 0x2401a0b0) ∗
      (bv_unsigned sp + 24) ↦ₘ (BV 64 0x177a8) ∗
      True)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Definition allocatorInstrMap : gmap (bv 64) isla_trace :=
  <[Z_to_bv 64 0x14ce8 := a14ce8]>
  (<[Z_to_bv 64 0x14ce4 := a14ce4]>
  (<[Z_to_bv 64 0x14ce0 := a14ce0]>
  (<[Z_to_bv 64 0x14cdc := a14cdc]>
  (<[Z_to_bv 64 0x14cd8 := a14cd8]>
  (<[Z_to_bv 64 0x14cd4 := a14cd4]>
  (<[Z_to_bv 64 0x14cd0 := a14cd0]>
  (<[Z_to_bv 64 0x14ccc := a14ccc]> ∅))))))).

Definition allocatorSetPc (pc : Z) (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits (Z_to_bv 64 pc)]> regs.

Definition allocatorR1 regs : reg_map :=
  allocatorSetPc 0x14cd0
    (<["x10" := RVal_Bits (Z_to_bv 64 0x24019ccc)]> regs).
Definition allocatorR2 regs : reg_map :=
  allocatorSetPc 0x14cd4
    (<["x11" := RVal_Bits (Z_to_bv 64 0x17cd0)]> regs).
Definition allocatorR3 stack8 regs : reg_map :=
  allocatorSetPc 0x14cd8 (<["x13" := RVal_Bits stack8]> regs).
Definition allocatorR4 stack0 regs : reg_map :=
  allocatorSetPc 0x14cdc (<["x12" := RVal_Bits stack0]> regs).
Definition allocatorR5 regs : reg_map :=
  allocatorSetPc 0x14ce0
    (<["x10" := RVal_Bits (Z_to_bv 64 0x2401a0b0)]> regs).
Definition allocatorR6 regs : reg_map :=
  allocatorSetPc 0x14ce4
    (<["x11" := RVal_Bits (Z_to_bv 64 0x177a8)]> regs).
Definition allocatorR7 regs : reg_map := allocatorSetPc 0x14ce8 regs.
Definition allocatorR8 regs : reg_map := allocatorSetPc 0x14cec regs.

Definition allocatorState := operationalState allocatorInstrMap.

Lemma allocatorPcR1 regs :
  allocatorR1 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd0)).
Proof. unfold allocatorR1, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR2 regs :
  allocatorR2 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd4)).
Proof. unfold allocatorR2, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR3 regs value :
  allocatorR3 value regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd8)).
Proof. unfold allocatorR3, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR4 regs value :
  allocatorR4 value regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cdc)).
Proof. unfold allocatorR4, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR5 regs :
  allocatorR5 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce0)).
Proof. unfold allocatorR5, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR6 regs :
  allocatorR6 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce4)).
Proof. unfold allocatorR6, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR7 regs :
  allocatorR7 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce8)).
Proof. unfold allocatorR7, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorPcR8 regs :
  allocatorR8 regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cec)).
Proof. unfold allocatorR8, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Ltac allocator_update_lookup :=
  intros Hlookup;
  unfold allocatorR8, allocatorR7, allocatorR6, allocatorR5,
    allocatorR4, allocatorR3, allocatorR2, allocatorR1, allocatorSetPc;
  simplify_map_eq; first [reflexivity | exact Hlookup].

Lemma allocatorR1X11 regs value :
  regs !! "x11" = Some (RVal_Bits value) ->
  allocatorR1 regs !! "x11" = Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR2X2 regs value :
  regs !! "x2" = Some (RVal_Bits value) ->
  allocatorR2 (allocatorR1 regs) !! "x2" = Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR2X13 regs value :
  regs !! "x13" = Some (RVal_Bits value) ->
  allocatorR2 (allocatorR1 regs) !! "x13" = Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR3X2 regs stack8 value :
  regs !! "x2" = Some (RVal_Bits value) ->
  allocatorR3 stack8 (allocatorR2 (allocatorR1 regs)) !! "x2" =
    Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR3X12 regs stack8 value :
  regs !! "x12" = Some (RVal_Bits value) ->
  allocatorR3 stack8 (allocatorR2 (allocatorR1 regs)) !! "x12" =
    Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR4X10 regs stack8 stack0 :
  allocatorR4 stack0
      (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs))) !! "x10" =
    Some (RVal_Bits (Z_to_bv 64 0x24019ccc)).
Proof. unfold allocatorR4, allocatorR3, allocatorR2, allocatorR1,
    allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorR5X11 regs stack8 stack0 :
  allocatorR5
      (allocatorR4 stack0
        (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs)))) !! "x11" =
    Some (RVal_Bits (Z_to_bv 64 0x17cd0)).
Proof. unfold allocatorR5, allocatorR4, allocatorR3, allocatorR2,
    allocatorR1, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorR6X2 regs stack8 stack0 value :
  regs !! "x2" = Some (RVal_Bits value) ->
  allocatorR6
      (allocatorR5
        (allocatorR4 stack0
          (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs))))) !! "x2" =
    Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR6X10 regs stack8 stack0 :
  allocatorR6
      (allocatorR5
        (allocatorR4 stack0
          (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs))))) !! "x10" =
    Some (RVal_Bits (Z_to_bv 64 0x2401a0b0)).
Proof. unfold allocatorR6, allocatorR5, allocatorR4, allocatorR3,
    allocatorR2, allocatorR1, allocatorSetPc. simplify_map_eq. reflexivity. Qed.

Lemma allocatorR7X2 regs stack8 stack0 value :
  regs !! "x2" = Some (RVal_Bits value) ->
  allocatorR7
      (allocatorR6
        (allocatorR5
          (allocatorR4 stack0
            (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs)))))) !! "x2" =
    Some (RVal_Bits value).
Proof. allocator_update_lookup. Qed.

Lemma allocatorR7X11 regs stack8 stack0 :
  allocatorR7
      (allocatorR6
        (allocatorR5
          (allocatorR4 stack0
            (allocatorR3 stack8 (allocatorR2 (allocatorR1 regs)))))) !! "x11" =
    Some (RVal_Bits (Z_to_bv 64 0x177a8)).
Proof. unfold allocatorR7, allocatorR6, allocatorR5, allocatorR4,
    allocatorR3, allocatorR2, allocatorR1, allocatorSetPc.
  simplify_map_eq. reflexivity. Qed.

Definition allocatorSystemContext (regs : reg_map) : Prop :=
  regs !! "rv_enable_pmp" = Some (RVal_Bool false) /\
  regs !! "rv_enable_misaligned_access" = Some (RVal_Bool false) /\
  regs !! "rv_ram_base" = Some (RVal_Bits (Z_to_bv 64 0x20000000)) /\
  regs !! "rv_ram_size" = Some (RVal_Bits (Z_to_bv 64 0x20000000)) /\
  regs !! "rv_rom_base" = Some (RVal_Bits (Z_to_bv 64 0x1000)) /\
  regs !! "rv_rom_size" = Some (RVal_Bits (Z_to_bv 64 0x100)) /\
  regs !! "rv_clint_base" = Some (RVal_Bits (Z_to_bv 64 0x2000000)) /\
  regs !! "rv_clint_size" = Some (RVal_Bits (Z_to_bv 64 0xc0000)) /\
  regs !! "rv_htif_tohost" = Some (RVal_Bits (Z_to_bv 64 0x40001000)) /\
  regs !! "cur_privilege" = Some (RVal_Enum "Machine") /\
  regs !! "misa" = Some (RegVal_Struct
    [("bits", RVal_Bits (Z_to_bv 64 0x8000000000001100))]) /\
  regs !! "mstatus" = Some (RegVal_Struct
    [("bits", RVal_Bits (Z_to_bv 64 0))]) /\
  regs !! "satp" = Some (RVal_Bits (Z_to_bv 64 0)).

Lemma allocatorSystemContextR1 regs :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR1 regs).
Proof. unfold allocatorSystemContext, allocatorR1, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR2 regs :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR2 regs).
Proof. unfold allocatorSystemContext, allocatorR2, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR3 regs value :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR3 value regs).
Proof. unfold allocatorSystemContext, allocatorR3, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR4 regs value :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR4 value regs).
Proof. unfold allocatorSystemContext, allocatorR4, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR5 regs :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR5 regs).
Proof. unfold allocatorSystemContext, allocatorR5, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR6 regs :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR6 regs).
Proof. unfold allocatorSystemContext, allocatorR6, allocatorSetPc.
  simplify_map_eq. tauto. Qed.
Lemma allocatorSystemContextR7 regs :
  allocatorSystemContext regs -> allocatorSystemContext (allocatorR7 regs).
Proof. unfold allocatorSystemContext, allocatorR7, allocatorSetPc.
  simplify_map_eq. tauto. Qed.

Ltac allocator_lookup_context :=
  unfold allocatorSystemContext in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  simplify_map_eq;
  eauto;
  try apply readAccessorZToBv;
  try bv_solve.

Lemma allocatorAuipc10StepAny (regs : reg_map) (mem : mem_map) x10 :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ccc)) ->
  regs !! "x10" = Some (RVal_Bits x10) ->
  operationalInstructionStep 0 (allocatorState regs mem)
    (allocatorState (allocatorR1 regs) mem).
Proof.
  intros Hsys HPC Hx10.
  operational_begin_instruction (Z_to_bv 64 0x14ccc) a14ccc.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR1 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
Qed.

Lemma allocatorAuipc11StepAny (regs : reg_map) (mem : mem_map) x11 :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd0)) ->
  regs !! "x11" = Some (RVal_Bits x11) ->
  operationalInstructionStep 1 (allocatorState regs mem)
    (allocatorState (allocatorR2 regs) mem).
Proof.
  intros Hsys HPC Hx11.
  operational_begin_instruction (Z_to_bv 64 0x14cd0) a14cd0.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR2 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
Qed.

Lemma allocatorLoad13StepAny (regs : reg_map) (mem : mem_map)
    (sp oldX13 stack8 : bv 64) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x13" = Some (RVal_Bits oldX13) ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp ->
  bv_unsigned sp + 24 < 0x40000000 ->
  read_mem mem (bv_unsigned sp + 8) 8 = Some (bv_to_bvn stack8) ->
  operationalInstructionStep 2 (allocatorState regs mem)
    (allocatorState (allocatorR3 stack8 regs) mem).
Proof.
  intros Hsys HPC Hsp Hx13 Halign Hlow Hhigh Hmem.
  pose proof (bvExtractLowThreeZero sp Halign) as Hextract.
  operational_begin_instruction (Z_to_bv 64 0x14cd4) a14cd4.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; exact Hextract).
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; bv_solve).
  all: assert (Haddr : bv_unsigned (sp + Z_to_bv 64 8)%bv =
      bv_unsigned sp + 8) by bv_solve.
  all: try rewrite Haddr.
  all: try rewrite Hmem.
  all: repeat first [split | left]; try reflexivity.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR3 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  replace (bv_sign_extend (0 + 64) stack8) with stack8 by bv_solve.
  replace (Z_to_bv 64 0x14cd4 + Z_to_bv 64 4)%bv
    with (Z_to_bv 64 0x14cd8) by bv_solve.
  constructor.
Qed.

Lemma allocatorLoad12StepAny (regs : reg_map) (mem : mem_map)
    (sp oldX12 stack0 : bv 64) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cd8)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x12" = Some (RVal_Bits oldX12) ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp ->
  bv_unsigned sp + 24 < 0x40000000 ->
  read_mem mem (bv_unsigned sp) 8 = Some (bv_to_bvn stack0) ->
  operationalInstructionStep 3 (allocatorState regs mem)
    (allocatorState (allocatorR4 stack0 regs) mem).
Proof.
  intros Hsys HPC Hsp Hx12 Halign Hlow Hhigh Hmem.
  pose proof (bvExtractLowThreeZero sp Halign) as Hextract.
  operational_begin_instruction (Z_to_bv 64 0x14cd8) a14cd8.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; exact Hextract).
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; bv_solve).
  all: try rewrite Hmem.
  all: repeat first [split | left].
  all: try reflexivity.
  all: assert (Haddr : bv_unsigned (sp + Z_to_bv 64 0)%bv =
      bv_unsigned sp) by bv_solve.
  all: try rewrite Haddr.
  all: try rewrite Hmem.
  all: repeat first [split | left].
  all: try reflexivity.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR4 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  replace (bv_sign_extend (0 + 64) stack0) with stack0 by bv_solve.
  replace (Z_to_bv 64 0x14cd8 + Z_to_bv 64 4)%bv
    with (Z_to_bv 64 0x14cdc) by bv_solve.
  constructor.
Qed.

Lemma allocatorAdd10StepAny (regs : reg_map) (mem : mem_map) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14cdc)) ->
  regs !! "x10" = Some (RVal_Bits (Z_to_bv 64 0x24019ccc)) ->
  operationalInstructionStep 4 (allocatorState regs mem)
    (allocatorState (allocatorR5 regs) mem).
Proof.
  intros Hsys HPC Hx10.
  operational_begin_instruction (Z_to_bv 64 0x14cdc) a14cdc.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR5 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
Qed.

Lemma allocatorAdd11StepAny (regs : reg_map) (mem : mem_map) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce0)) ->
  regs !! "x11" = Some (RVal_Bits (Z_to_bv 64 0x17cd0)) ->
  operationalInstructionStep 5 (allocatorState regs mem)
    (allocatorState (allocatorR6 regs) mem).
Proof.
  intros Hsys HPC Hx11.
  operational_begin_instruction (Z_to_bv 64 0x14ce0) a14ce0.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR6 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
  assert (Hregs :
      <["PC" := RVal_Bits
          (Z_to_bv 64 0x14ce0 + Z_to_bv 64 4)%bv]>
        (<["x11" := RVal_Bits
            (Z_to_bv 64 0x17cd0 +
              Z_to_bv 64 0xfffffffffffffad8)%bv]> regs) =
      allocatorR6 regs).
  { unfold allocatorR6, allocatorSetPc.
    repeat f_equal; apply bv_eq; bv_solve. }
  rewrite Hregs.
  constructor.
Qed.

Lemma allocatorStore10StepAny (regs : reg_map) (mem : mem_map)
    (sp x10 : bv 64) (old : bvn) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits x10) ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp ->
  bv_unsigned sp + 24 < 0x40000000 ->
  read_mem mem (bv_unsigned sp + 16) 8 = Some old ->
  operationalInstructionStep 6 (allocatorState regs mem)
    (allocatorState (allocatorR7 regs)
      (write_mem 8 mem (sp + Z_to_bv 64 16)%bv (bv_unsigned x10))).
Proof.
  intros Hsys HPC Hsp Hx10 Halign Hlow Hhigh Hmem.
  pose proof (bvExtractLowThreeZero sp Halign) as Hextract.
  operational_begin_instruction (Z_to_bv 64 0x14ce4) a14ce4.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; exact Hextract).
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; bv_solve).
  all: assert (Haddr : bv_unsigned (sp + Z_to_bv 64 16)%bv =
      bv_unsigned sp + 16) by bv_solve.
  all: try rewrite Haddr.
  all: try rewrite Hmem.
  all: repeat first [split | left].
  all: try reflexivity.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR7 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: exact false.
Qed.

Lemma allocatorStore11StepAny (regs : reg_map) (mem : mem_map)
    (sp x11 : bv 64) (old : bvn) :
  allocatorSystemContext regs ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ce8)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some (RVal_Bits x11) ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp ->
  bv_unsigned sp + 24 < 0x40000000 ->
  read_mem mem (bv_unsigned sp + 24) 8 = Some old ->
  operationalInstructionStep 7 (allocatorState regs mem)
    (allocatorState (allocatorR8 regs)
      (write_mem 8 mem (sp + Z_to_bv 64 24)%bv (bv_unsigned x11))).
Proof.
  intros Hsys HPC Hsp Hx11 Halign Hlow Hhigh Hmem.
  pose proof (bvExtractLowThreeZero sp Halign) as Hextract.
  operational_begin_instruction (Z_to_bv 64 0x14ce8) a14ce8.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; exact Hextract).
  all: try (f_equal; f_equal; apply bool_decide_eq_true_2; bv_solve).
  all: assert (Haddr : bv_unsigned (sp + Z_to_bv 64 24)%bv =
      bv_unsigned sp + 24) by bv_solve.
  all: try rewrite Haddr.
  all: try rewrite Hmem.
  all: repeat first [split | left].
  all: try reflexivity.
  repeat operational_trace_step_visible.
  all: allocator_lookup_context.
  all: cbn [allocatorR8 allocatorSetPc] in *.
  all: simplify_map_eq.
  all: try bv_solve.
  all: try constructor.
  Unshelve. all: exact false.
Qed.

Definition allocatorMem1 (sp : bv 64) (mem : mem_map) : mem_map :=
  write_mem 8 mem (sp + Z_to_bv 64 16)%bv 0x2401a0b0.

Definition allocatorMem2 (sp : bv 64) (mem : mem_map) : mem_map :=
  write_mem 8 (allocatorMem1 sp mem)
    (sp + Z_to_bv 64 24)%bv 0x177a8.

Definition allocatorCanonicalEntry (args : AllocatorGetArgs)
    (state : OperationalState) : Prop :=
  exists (sp x10 x11 x12 x13 stack0 stack8 : bv 64) regs
      mem old16 old24,
    bv_unsigned sp = allocatorStackPointer args /\
    bv_unsigned sp `mod` 8 = 0 /\
    0x20000000 <= bv_unsigned sp /\
    bv_unsigned sp + 24 < 0x40000000 /\
    read_mem mem (bv_unsigned sp) 8 = Some (bv_to_bvn stack0) /\
    read_mem mem (bv_unsigned sp + 8) 8 = Some (bv_to_bvn stack8) /\
    read_mem mem (bv_unsigned sp + 16) 8 = Some old16 /\
    read_mem (allocatorMem1 sp mem) (bv_unsigned sp + 24) 8 = Some old24 /\
    allocatorSystemContext regs /\
    regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ccc)) /\
    regs !! "x2" = Some (RVal_Bits sp) /\
    regs !! "x10" = Some (RVal_Bits x10) /\
    regs !! "x11" = Some (RVal_Bits x11) /\
    regs !! "x12" = Some (RVal_Bits x12) /\
    regs !! "x13" = Some (RVal_Bits x13) /\
    state = allocatorState regs mem.

Definition allocatorCanonicalPost (args : AllocatorGetArgs)
    (outcome : AllocatorGetOutcome) (before after : OperationalState) : Prop :=
  exists (sp x10 x11 x12 x13 stack0 stack8 : bv 64) regs mem,
    bv_unsigned sp = allocatorStackPointer args /\
    outcome = Build_AllocatorGetOutcome 0x2401a0b0 0x177a8 /\
    before = allocatorState regs mem /\
    after = allocatorState
      (allocatorR8
        (allocatorR7
          (allocatorR6
            (allocatorR5
              (allocatorR4 stack0
                (allocatorR3 stack8
                  (allocatorR2
                    (allocatorR1
                      regs))))))))
      (allocatorMem2 sp mem).

Definition allocatorCanonicalModel :
    Level1MachineModel OperationalState unit := {|
  endpointStep := operationalInstructionStep;
  endpointPc := operationalPc;
  readInputEntry := fun _ _ => False;
  readInputExit := fun _ _ _ _ => False;
  allocatorGetEntry := allocatorCanonicalEntry;
  allocatorGetExit := allocatorCanonicalPost;
  decodeBoundaryEntry := fun _ _ => False;
  decodeBoundaryExit := fun _ _ _ _ => False;
  writeSuccessEntry := fun _ _ => False;
  writeSuccessExit := fun _ _ _ _ => False;
  writeFailureEntry := fun _ _ => False;
  writeFailureExit := fun _ _ _ _ => False;
  zkvmExitEntry := fun _ _ => False;
  zkvmExitPost := fun _ _ _ _ => False;
  referenceDecodes := fun _ _ => False;
  decodedResultRelModuloKnownBugs := fun _ _ _ => False;
  avoidsReviewedDomainDivergences := fun _ _ => False;
  knownBugApplies := fun _ _ _ => False;
  decodeObservationSuccess := fun _ _ => False;
  decodeObservationFailure := fun _ => False
|}.

Ltac allocator_region :=
  unfold PcInRanges;
  eexists 0x14ccc, 0x14cec; split;
  [ cbn; left; reflexivity | lia ].

Lemma allocatorCanonicalImplements :
  Implements allocatorCanonicalModel
    (PcInRanges allocatorGetExecutionPcRanges)
    (PcInList allocatorGetExitPcs)
    (allocatorGetContract allocatorCanonicalModel (fun _ => 8%nat)).
Proof.
  unfold Implements, ContractImplements.
  intros args fromStep before
    (sp & x10 & x11 & x12 & x13 & stack0 & stack8 & regs & mem &
      old16 & old24 & HspValue & Halign & Hlow & Hhigh & Hread0 &
      Hread8 & Hread16 & Hread24 & Hsys0 & Hpc0 & Hx20 & Hx100 &
      Hx110 & Hx120 & Hx130 & ->).
  set r1 := allocatorR1 regs.
  set r2 := allocatorR2 r1.
  set r3 := allocatorR3 stack8 r2.
  set r4 := allocatorR4 stack0 r3.
  set r5 := allocatorR5 r4.
  set r6 := allocatorR6 r5.
  set r7 := allocatorR7 r6.
  set r8 := allocatorR8 r7.
  set mem1 := allocatorMem1 sp mem.
  set mem2 := allocatorMem2 sp mem.
  assert (Hsys1 : allocatorSystemContext r1).
  { unfold r1. apply allocatorSystemContextR1. exact Hsys0. }
  assert (Hsys2 : allocatorSystemContext r2).
  { unfold r2. apply allocatorSystemContextR2. exact Hsys1. }
  assert (Hsys3 : allocatorSystemContext r3).
  { unfold r3. apply allocatorSystemContextR3. exact Hsys2. }
  assert (Hsys4 : allocatorSystemContext r4).
  { unfold r4. apply allocatorSystemContextR4. exact Hsys3. }
  assert (Hsys5 : allocatorSystemContext r5).
  { unfold r5. apply allocatorSystemContextR5. exact Hsys4. }
  assert (Hsys6 : allocatorSystemContext r6).
  { unfold r6. apply allocatorSystemContextR6. exact Hsys5. }
  assert (Hsys7 : allocatorSystemContext r7).
  { unfold r7. apply allocatorSystemContextR7. exact Hsys6. }
  assert (Hpc1 : r1 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd0))).
  { unfold r1. apply allocatorPcR1. }
  assert (Hpc2 : r2 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd4))).
  { unfold r2. apply allocatorPcR2. }
  assert (Hpc3 : r3 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd8))).
  { unfold r3. apply allocatorPcR3. }
  assert (Hpc4 : r4 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cdc))).
  { unfold r4. apply allocatorPcR4. }
  assert (Hpc5 : r5 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce0))).
  { unfold r5. apply allocatorPcR5. }
  assert (Hpc6 : r6 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce4))).
  { unfold r6. apply allocatorPcR6. }
  assert (Hpc7 : r7 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce8))).
  { unfold r7. apply allocatorPcR7. }
  assert (Hpc8 : r8 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cec))).
  { unfold r8. apply allocatorPcR8. }
  assert (Hx111 : r1 !! "x11" = Some (RVal_Bits x11)).
  { unfold r1. apply allocatorR1X11. exact Hx110. }
  assert (Hx22 : r2 !! "x2" = Some (RVal_Bits sp)).
  { unfold r2, r1. apply allocatorR2X2. exact Hx20. }
  assert (Hx132 : r2 !! "x13" = Some (RVal_Bits x13)).
  { unfold r2, r1. apply allocatorR2X13. exact Hx130. }
  assert (Hx23 : r3 !! "x2" = Some (RVal_Bits sp)).
  { unfold r3, r2, r1. apply allocatorR3X2. exact Hx20. }
  assert (Hx123 : r3 !! "x12" = Some (RVal_Bits x12)).
  { unfold r3, r2, r1. apply allocatorR3X12. exact Hx120. }
  assert (Hx104 : r4 !! "x10" =
      Some (RVal_Bits (Z_to_bv 64 0x24019ccc))).
  { unfold r4, r3, r2, r1. apply allocatorR4X10. }
  assert (Hx115 : r5 !! "x11" =
      Some (RVal_Bits (Z_to_bv 64 0x17cd0))).
  { unfold r5, r4, r3, r2, r1. apply allocatorR5X11. }
  assert (Hx26 : r6 !! "x2" = Some (RVal_Bits sp)).
  { unfold r6, r5, r4, r3, r2, r1.
    apply allocatorR6X2. exact Hx20. }
  assert (Hx106 : r6 !! "x10" =
      Some (RVal_Bits (Z_to_bv 64 0x2401a0b0))).
  { unfold r6, r5, r4, r3, r2, r1. apply allocatorR6X10. }
  assert (Hx27 : r7 !! "x2" = Some (RVal_Bits sp)).
  { unfold r7, r6, r5, r4, r3, r2, r1.
    apply allocatorR7X2. exact Hx20. }
  assert (Hx117 : r7 !! "x11" =
      Some (RVal_Bits (Z_to_bv 64 0x177a8))).
  { unfold r7, r6, r5, r4, r3, r2, r1. apply allocatorR7X11. }
  eexists 8%nat, (allocatorState r8 mem2),
    {| allocatorStateAddress := 0x2401a0b0;
       allocatorVtableAddress := 0x177a8 |}.
  repeat split.
  - lia.
  - reflexivity.
  - eapply ConfinedTraceStep with
      (address := 0x14ccc) (middle := allocatorState r1 mem).
    + cbn. rewrite Hpc0. reflexivity.
    + allocator_region.
    + eapply allocatorAuipc10StepAny; eauto.
    + eapply ConfinedTraceStep with
        (address := 0x14cd0) (middle := allocatorState r2 mem).
      * cbn. rewrite Hpc1. reflexivity.
      * allocator_region.
      * eapply allocatorAuipc11StepAny.
        -- exact Hsys1.
        -- exact Hpc1.
        -- exact Hx111.
      * eapply ConfinedTraceStep with
          (address := 0x14cd4) (middle := allocatorState r3 mem).
        -- cbn. rewrite Hpc2. reflexivity.
        -- allocator_region.
        -- eapply allocatorLoad13StepAny with
             (sp := sp) (oldX13 := x13) (stack8 := stack8).
           ++ exact Hsys2.
           ++ exact Hpc2.
           ++ exact Hx22.
           ++ exact Hx132.
           ++ exact Halign.
           ++ exact Hlow.
           ++ exact Hhigh.
           ++ exact Hread8.
        -- eapply ConfinedTraceStep with
            (address := 0x14cd8) (middle := allocatorState r4 mem).
           ++ cbn. rewrite Hpc3. reflexivity.
           ++ allocator_region.
           ++ eapply allocatorLoad12StepAny with
                (sp := sp) (oldX12 := x12) (stack0 := stack0).
              ** exact Hsys3.
              ** exact Hpc3.
              ** exact Hx23.
              ** exact Hx123.
              ** exact Halign.
              ** exact Hlow.
              ** exact Hhigh.
              ** exact Hread0.
           ++ eapply ConfinedTraceStep with
               (address := 0x14cdc) (middle := allocatorState r5 mem).
              ** cbn. rewrite Hpc4. reflexivity.
              ** allocator_region.
              ** apply allocatorAdd10StepAny.
                 --- exact Hsys4.
                 --- exact Hpc4.
                 --- exact Hx104.
              ** eapply ConfinedTraceStep with
                  (address := 0x14ce0) (middle := allocatorState r6 mem).
                 --- cbn. rewrite Hpc5. reflexivity.
                 --- allocator_region.
                 --- apply allocatorAdd11StepAny.
                     +++ exact Hsys5.
                     +++ exact Hpc5.
                     +++ exact Hx115.
                 --- eapply ConfinedTraceStep with
                     (address := 0x14ce4)
                     (middle := allocatorState r7 mem1).
                     +++ cbn. rewrite Hpc6. reflexivity.
                     +++ allocator_region.
                     +++ eapply allocatorStore10StepAny with
                           (sp := sp) (x10 := Z_to_bv 64 0x2401a0b0)
                           (old := old16).
                         *** exact Hsys6.
                         *** exact Hpc6.
                         *** exact Hx26.
                         *** exact Hx106.
                         *** exact Halign.
                         *** exact Hlow.
                         *** exact Hhigh.
                         *** exact Hread16.
                     +++ eapply ConfinedTraceStep with
                         (address := 0x14ce8)
                         (middle := allocatorState r8 mem2).
                         *** cbn. rewrite Hpc7. reflexivity.
                         *** allocator_region.
                         *** eapply allocatorStore11StepAny with
                               (sp := sp) (x11 := Z_to_bv 64 0x177a8)
                               (old := old24).
                             ---- exact Hsys7.
                             ---- exact Hpc7.
                             ---- exact Hx27.
                             ---- exact Hx117.
                             ---- exact Halign.
                             ---- exact Hlow.
                             ---- exact Hhigh.
                             ---- subst mem1. exact Hread24.
                         *** constructor.
  - eexists 0x14cec. split.
    + cbn. rewrite Hpc8. reflexivity.
    + cbn. left. reflexivity.
  - cbn.
    eexists sp, x10, x11, x12, x13, stack0, stack8, regs, mem.
    repeat split; try assumption.
Qed.

Theorem level1AllocatorCanonical :
  exists bound, InputIndexedBound bound /\
    Implements allocatorCanonicalModel
      (PcInRanges allocatorGetExecutionPcRanges)
      (PcInList allocatorGetExitPcs)
      (allocatorGetContract allocatorCanonicalModel
        (fun args => bound (length (allocatorInput args)))).
Proof.
  eexists (fun _ => 8%nat). split.
  - intros size _. unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - exact allocatorCanonicalImplements.
Qed.
