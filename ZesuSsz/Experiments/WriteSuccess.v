From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_00 Require Import instrs.
From IslaTraces.write_success_14 Require Import instrs.
From IslaTraces.write_success_15 Require Import instrs.
From IslaTraces.write_success_16 Require Import instrs.
From IslaTraces.write_success_17 Require Import instrs.
From IslaTraces.write_success_18 Require Import instrs.
From IslaTraces.write_success_19 Require Import instrs.
From IslaTraces.write_success_20 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.

Import ListNotations.

Lemma bv_sign_extend_64_idemp (b : bv 64) : bv_sign_extend 64 b = b.
Proof. apply bv_sign_extend_idemp. Qed.

Lemma bv_zero_extend_64_zero_8 (b : bv 8) :
  bv_zero_extend 64 b = BV 64 0 -> b = BV 8 0.
Proof.
  move => Hzero.
  apply bv_eq.
  move: (f_equal bv_unsigned Hzero).
  rewrite bv_zero_extend_unsigned // !bv_unsigned_BV //.
Qed.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Definition writeSuccessOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7";
   "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessOtherRegisters.

Definition writeSuccessScratch `{!islaG Sigma} `{!threadG}
    (sp : bv 64) : iProp Sigma :=
  (∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : bv 64,
    (bv_unsigned sp - 0x68) ↦ₘ v0 ∗ (bv_unsigned sp - 0x60) ↦ₘ v1 ∗
    (bv_unsigned sp - 0x58) ↦ₘ v2 ∗ (bv_unsigned sp - 0x50) ↦ₘ v3 ∗
    (bv_unsigned sp - 0x48) ↦ₘ v4 ∗ (bv_unsigned sp - 0x40) ↦ₘ v5 ∗
    (bv_unsigned sp - 0x38) ↦ₘ v6 ∗ (bv_unsigned sp - 0x30) ↦ₘ v7 ∗
    (bv_unsigned sp - 0x28) ↦ₘ v8 ∗ (bv_unsigned sp - 0x20) ↦ₘ v9 ∗
    (bv_unsigned sp - 0x18) ↦ₘ v10 ∗ (bv_unsigned sp - 0x10) ↦ₘ v11 ∗
    (bv_unsigned sp - 0x8) ↦ₘ v12 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessScratch) := I.

Definition writeSuccessSavedSlots `{!islaG Sigma} `{!threadG}
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp - 0x68) ↦ₘ s11 ∗ (bv_unsigned sp - 0x60) ↦ₘ s10 ∗
   (bv_unsigned sp - 0x58) ↦ₘ s9 ∗ (bv_unsigned sp - 0x50) ↦ₘ s8 ∗
   (bv_unsigned sp - 0x48) ↦ₘ s7 ∗ (bv_unsigned sp - 0x40) ↦ₘ s6 ∗
   (bv_unsigned sp - 0x38) ↦ₘ s5 ∗ (bv_unsigned sp - 0x30) ↦ₘ s4 ∗
   (bv_unsigned sp - 0x28) ↦ₘ s3 ∗ (bv_unsigned sp - 0x20) ↦ₘ s2 ∗
   (bv_unsigned sp - 0x18) ↦ₘ s1 ∗ (bv_unsigned sp - 0x10) ↦ₘ s0 ∗
   (bv_unsigned sp - 0x8) ↦ₘ ra ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSavedSlots) := I.

Definition write_success_prologue_entry `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   "x10" ↦ᵣ RVal_Bits decoded ∗ "x11" ↦ᵣ: (fun _ =>
   "x12" ↦ᵣ: (fun _ =>
   ⌜bv_unsigned decoded = (bv_unsigned sp + 0x20)%Z⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(0x20000880 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 0x7d0 < 0x40000000)%Z⌝ ∗
   writeSuccessScratch sp ∗ P ∗ True)))%I.

Global Instance : LithiumUnfold (@write_success_prologue_entry) := I.

Definition write_success_prologue_exit `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0xfd78) ∗
   "x2" ↦ᵣ RVal_Bits ((sp - (BV 64 0x7d0))%bv) ∗
   "x8" ↦ᵣ RVal_Bits decoded ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   "x10" ↦ᵣ RVal_Bits ((sp - (BV 64 0x698))%bv) ∗
   "x11" ↦ᵣ RVal_Bits decoded ∗
   "x12" ↦ᵣ RVal_Bits (BV 64 720) ∗
   writeSuccessSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold (@write_success_prologue_exit) := I.

Lemma write_success_prologue `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_00.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14d30
    (write_success_prologue_entry sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11 P ∗
     instr_pre 0x14d7c
       (write_success_prologue_exit sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
          s8 s9 s10 s11 P) ∗ True).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith H1).
  all: try bv_solve.
  all: try lia.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition writeOutputEvents (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

Ltac close_infeasible_bv_branches :=
  match goal with
  | Hneq : ?left ≠ ?right |- _ =>
      try solve [iExFalso; iPureIntro; apply Hneq; bv_solve]
  | _ : _ = false |- _ => try solve [iExFalso; iPureIntro; bv_solve]
  | _ : false = _ |- _ => try solve [iExFalso; iPureIntro; bv_solve]
  | _ => idtac
  end.

Definition encoderOptionalSomeSpec `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 old_x11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 16 - BV 64 16 + BV 64 7)%bv)
        (BV 64 1)
        (writeOutputEvents ((sp - BV 64 16)%bv) (BV 64 8) tail)) ∗
    ⌜tag ≠ BV 8 0⌝ ∗
    ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
    ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 32)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (∃ (final_x6 : bv 64),
       reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x6" ↦ᵣ RVal_Bits final_x6 ∗ "x8" ↦ᵣ RVal_Bits old_x8 ∗
       "x10" ↦ᵣ RVal_Bits ((sp - BV 64 16)%bv) ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
       bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
       (bv_unsigned sp - 32) ↦ₘ? 8 ∗
       (bv_unsigned sp - 24) ↦ₘ? 8 ∗
       (bv_unsigned sp - 16) ↦ₘ? 8 ∗
       (bv_unsigned sp - 8) ↦ₘ? 8 ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeSpec) := I.

Lemma encoder_optional_some_correct `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_17.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8
    (encoderOptionalSomeSpec data value sp ret tag tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 data = _)).
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: try match goal with
           | Hneq : ?tag ≠ (BV 8 0) |- _ =>
               match goal with
               | Hzero : bv_zero_extend 64 tag = (BV 64 0) |- _ =>
                   exfalso; apply Hneq;
                   exact (bv_zero_extend_64_zero_8 tag Hzero)
               end
           end.
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition writeOutputEntry `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_data old_size : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    0x2401a0c0 ↦ₘ old_data ∗ 0x2401a0c8 ↦ₘ old_size ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputEntry) := I.

Definition writeOutputExit `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   0x2401a0c0 ↦ₘ data ∗ 0x2401a0c8 ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputExit) := I.

Lemma write_output_correct `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeOutputEntry data size ret P ∗
     instr_pre (bv_unsigned ret) (writeOutputExit data size ret P) ∗ True).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition writeOutputTraceSpec `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents data size tail) ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputTraceSpec) := I.

Lemma write_output_trace_correct `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 (writeOutputTraceSpec data size ret tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition zesuMemcpyLoopSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  ∃ (tmp13 tmp14 src dst n ret i : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma),
  reg_col zesu_ram_sys_regs ∗
  "x1" ↦ᵣ RVal_Bits ret ∗
  "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
  "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
  "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits i ∗
  bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
  ⌜bv_unsigned n = length srcdata⌝ ∗
  ⌜bv_unsigned n = length dstdata⌝ ∗
  ⌜(bv_unsigned i <= bv_unsigned n)%Z⌝ ∗
  ⌜(0x20000000 <= bv_unsigned src)%Z⌝ ∗
  ⌜(bv_unsigned src + bv_unsigned n < 0x40000000)%Z⌝ ∗
  ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗
  ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
  ⌜take (Z.to_nat (bv_unsigned i)) dstdata =
    take (Z.to_nat (bv_unsigned i)) srcdata⌝ ∗
  ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
  ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
  ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
  instr_pre (bv_unsigned ret)
    (∃ (final13 final14 : bv 64),
      reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits ret ∗
      "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
      "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
      "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits n ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      P ∗ True) ∗
  P ∗ True.

Global Instance : LithiumUnfold (@zesuMemcpyLoopSpec) := I.

Lemma zesu_memcpy_loop `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_15.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 zesuMemcpyLoopSpec -∗
  instr_body 0x101d8 zesuMemcpyLoopSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  - liARun.
    liShow.
    replace (bv_unsigned LET6) with
      (bv_unsigned src + Z.of_nat (Z.to_nat (bv_unsigned i)))%Z by bv_solve.
    iRename select (bv_unsigned src ↦ₘ∗ srcdata)%I into "Hsrc".
    have Hine : bv_unsigned i <> bv_unsigned n.
    { intro Heq. apply H12. apply bv_eq. exact Heq. }
    have Hiz : (bv_unsigned i < bv_unsigned n)%Z by lia.
    have Hi : (Z.to_nat (bv_unsigned i) < length srcdata)%nat.
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id; [rewrite <- H0; exact Hiz | bv_solve]. }
    have [srcbyte Hsrcbyte] := lookup_lt_is_Some_2 srcdata _ Hi.
    iDestruct (mem_mapsto_array_lookup_acc 8%N (bv_unsigned src)
      (Z.to_nat (bv_unsigned i)) srcdata (DfracOwn 1) 1%N srcbyte
      with "Hsrc") as "[Hsrcbyte Hsrcclose]";
      [done | exact Hsrcbyte |].
    liARun.
    iRename select
      ((bv_unsigned src + Z.to_nat (bv_unsigned i))%Z ↦ₘ srcbyte)%I
      into "HsrcbyteNow".
    iExists (P,
      <[Z.to_nat ((bv_unsigned LET15 - bv_unsigned dst) `div` 1) := LET16]>
        dstdata,
      srcdata, tt)ₗ.
    red_li_prod.
    iSplitL "Hsrcclose HsrcbyteNow".
    { have Hsrcaddr :
        (bv_unsigned src + Z.to_nat (bv_unsigned i) * 1 =
         bv_unsigned src + Z.to_nat (bv_unsigned i))%Z by lia.
      iEval (rewrite Hsrcaddr) in "Hsrcclose".
      iApply "Hsrcclose". iExact "HsrcbyteNow". }
    iFrame.
    liARun.
    iPureIntro. exact H10.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite length_insert.
  all: try bv_solve.
  all: try lia.
  { rewrite (take_ge dstdata) in H7.
    2: bv_solve.
    rewrite (take_ge srcdata) in H7.
    2: bv_solve.
    exact H7. }
  { replace (Z.to_nat (bv_unsigned (i + 1))) with
      (S (Z.to_nat (bv_unsigned i))) by bv_solve.
    erewrite take_S_r. 2: {
      erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
    erewrite take_S_r. 2: exact Hsrcbyte.
    rewrite take_insert; [|bv_solve].
    f_equal; [done|]. f_equal. bv_solve. }
Qed.

Lemma zesu_memcpy_loop_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_15.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 zesuMemcpyLoopSpec.
Proof.
  iStartProof.
  iIntros "#Hcode".
  iLöb as "IH".
  iModIntro.
  iApply instr_pre_to_body.
  iNext.
  iApply (zesu_memcpy_loop with "Hcode IH").
Qed.

Definition zesuMemcpySpec `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (tmp13 tmp14 tmp15 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
    "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
    "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits tmp15 ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗
    ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜(0x20000000 <= bv_unsigned src)%Z⌝ ∗
    ⌜(bv_unsigned src + bv_unsigned n < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗
    ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (∃ (final13 final14 : bv 64),
        reg_col zesu_ram_sys_regs ∗
        "x1" ↦ᵣ RVal_Bits ret ∗
        "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
        "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
        "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits n ∗
        bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
        P ∗ True) ∗
    P ∗ True)%I.

Global Instance : LithiumUnfold (@zesuMemcpySpec) := I.

Lemma zesu_memcpy_correct `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_15.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (zesuMemcpySpec dst src n ret srcdata dstdata P).
Proof.
  iStartProof.
  iIntros "#Hcode".
  iAssert (□ instr_pre 0x101d8 zesuMemcpyLoopSpec)%I as "#Hloop".
  { iLöb as "IH".
    iModIntro.
    iApply instr_pre_to_body.
    iNext.
    iApply zesu_memcpy_loop.
    - iExact "Hcode".
    - iExact "IH". }
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#H101d4 & #H101d8 & #H101dc & #H101e0 & #H101e4 & #H101e8 &
     #H101ec & #H101f0 & #H101f4 & _)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition encoderIntSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x11 stack0 stack8 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits value ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 16) ↦ₘ stack0 ∗
    (bv_unsigned sp - 8) ↦ₘ stack8 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents ((sp - BV 64 16)%bv) (BV 64 8) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x10" ↦ᵣ RVal_Bits ((sp - BV 64 16)%bv) ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
       (bv_unsigned sp - 16) ↦ₘ value ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderIntSpec) := I.

Lemma encoder_int_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (encoderIntSpec value sp ret tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition encoderBooleanSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x11 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits value ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 9)%bv) (BV 64 1) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x10" ↦ᵣ RVal_Bits ((sp - BV 64 9)%bv) ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
       (bv_unsigned sp - 16) ↦ₘ? 7 ∗
       (bv_unsigned sp - 9) ↦ₘ
         (bv_extract 0 8 (bv_and value (BV 64 1))) ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBooleanSpec) := I.

Lemma encoder_boolean_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (encoderBooleanSpec value sp ret tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition encoderBytesSpec `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_s0 old_s1
       stack0 stack1 stack2 stack3 stack4 stack5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ stack0 ∗
    (bv_unsigned sp - 40) ↦ₘ stack1 ∗
    (bv_unsigned sp - 32) ↦ₘ stack2 ∗
    (bv_unsigned sp - 24) ↦ₘ stack3 ∗
    (bv_unsigned sp - 16) ↦ₘ stack4 ∗
    (bv_unsigned sp - 8) ↦ₘ stack5 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 48)%bv) (BV 64 8)
        (writeOutputEvents data size tail)) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (∃ (final_x6 : bv 64),
       reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x6" ↦ᵣ RVal_Bits final_x6 ∗
       "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       (bv_unsigned sp - 48) ↦ₘ size ∗
       (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
       (bv_unsigned sp - 32) ↦ₘ stack2 ∗
       (bv_unsigned sp - 24) ↦ₘ old_s1 ∗
       (bv_unsigned sp - 16) ↦ₘ old_s0 ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       bv_unsigned data ↦ₘ∗ bytes ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBytesSpec) := I.

Lemma encoder_bytes_correct `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_19.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c (encoderBytesSpec data size sp ret bytes tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition encoderOptionalNoneSpec `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 old_x11 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    bv_unsigned data ↦ₘ value ∗
    (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 9)%bv) (BV 64 1) tail) ∗
    ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
    ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (∃ (final_x6 : bv 64),
       reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x6" ↦ᵣ RVal_Bits final_x6 ∗
       "x8" ↦ᵣ RVal_Bits old_x8 ∗
       "x10" ↦ᵣ RVal_Bits ((sp - BV 64 9)%bv) ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
       bv_unsigned data ↦ₘ value ∗
       (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
       (bv_unsigned sp - 16) ↦ₘ? 7 ∗
       (bv_unsigned sp - 9) ↦ₘ (BV 8 0) ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalNoneSpec) := I.

Lemma encoder_optional_none_correct `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_17.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (encoderOptionalNoneSpec data value sp ret tail P).
Proof.
  move => * /=.
  iStartProof.
  time "liARun"
    repeat (liAStep; close_infeasible_bv_branches).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
