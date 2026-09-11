Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Import ListNotations.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

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
    spec_trace (writeOutputEventsAny ((sp - BV 64 16)%bv) (BV 64 8) tail) ∗
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
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
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

