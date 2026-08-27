Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.OperationalBridge.
From IslaTraces.allocator_get Require Import instrs.

Definition allocatorInstrMap : gmap (bv 64) isla_trace :=
  <[Z_to_bv 64 0x14ce8 := a14ce8]>
  (<[Z_to_bv 64 0x14ce4 := a14ce4]>
  (<[Z_to_bv 64 0x14ce0 := a14ce0]>
  (<[Z_to_bv 64 0x14cdc := a14cdc]>
  (<[Z_to_bv 64 0x14cd8 := a14cd8]>
  (<[Z_to_bv 64 0x14cd4 := a14cd4]>
  (<[Z_to_bv 64 0x14cd0 := a14cd0]>
  (<[Z_to_bv 64 0x14ccc := a14ccc]> ∅))))))).

Definition allocatorAuipcInitialRegs (x10 x11 : bv 64) : reg_map :=
  <["mstatus" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]]>
  (<["misa" := RegVal_Struct [("bits", RVal_Bits
      (Z_to_bv 64 0x8000000000001100))]]>
  (<["x11" := RVal_Bits x11]>
  (<["x10" := RVal_Bits x10]>
  (<["PC" := RVal_Bits (Z_to_bv 64 0x14ccc)]> ∅)))).

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

Ltac finish_allocator_trace :=
  repeat operational_trace_step;
  try apply readAccessorZToBv;
  try bv_solve;
  try constructor.

Lemma allocatorAuipc10Step x10 x11 mem :
  operationalInstructionStep 0
    (allocatorState (allocatorAuipcInitialRegs x10 x11) mem)
    (allocatorState
      (allocatorR1 (allocatorAuipcInitialRegs x10 x11)) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x14ccc) a14ccc.
  finish_allocator_trace.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
Qed.

Lemma allocatorAuipc11Step x10 x11 mem :
  operationalInstructionStep 1
    (allocatorState
      (allocatorR1 (allocatorAuipcInitialRegs x10 x11)) mem)
    (allocatorState
      (allocatorR2 (allocatorR1
        (allocatorAuipcInitialRegs x10 x11))) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x14cd0) a14cd0.
  finish_allocator_trace.
  Unshelve. all: try (first [exact (Z_to_bv 64 0) | exact false]).
Qed.

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
