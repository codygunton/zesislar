Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Import ListNotations.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Definition encoderBytesSuffixFrame `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x8" ↦ᵣ RVal_Bits size ∗ "x9" ↦ᵣ RVal_Bits data ∗
   (bv_unsigned sp - 32) ↦ₘ stack2 ∗
   (bv_unsigned sp - 24) ↦ₘ old_s1 ∗
   (bv_unsigned sp - 16) ↦ₘ old_s0 ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   bv_unsigned data ↦ₘ∗ bytes ∗
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

Global Instance : LithiumUnfold (@encoderBytesSuffixFrame) := I.

Definition encoderBytesSuffixSpec `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15c90) ∗
   "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits ((sp - BV 64 32) - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned (sp - BV 64 32) - 16) ↦ₘ size ∗
   (bv_unsigned (sp - BV 64 32) - 8) ↦ₘ (BV 64 0x15c90) ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents data size tail) ∗
   encoderBytesSuffixFrame data size sp ret bytes
     old_x6 old_s0 old_s1 stack2 tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBytesSuffixSpec) := I.

Lemma encoder_bytes_suffix_correct `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr 0x15c90 (Some a15c90) -∗ instr 0x15c94 (Some a15c94) -∗
  instr 0x15c98 (Some a15c98) -∗ instr 0x15c9c (Some a15c9c) -∗
  instr 0x15ca0 (Some a15ca0) -∗ instr 0x15ca4 (Some a15ca4) -∗
  instr 0x15ca8 (Some a15ca8) -∗ instr 0x15cac (Some a15cac) -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c90
    (encoderBytesSuffixSpec data size sp ret bytes
      old_x6 old_s0 old_s1 stack2 tail P).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma encoder_bytes_suffix_pre `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr 0x15c90 (Some a15c90) -∗ instr 0x15c94 (Some a15c94) -∗
  instr 0x15c98 (Some a15c98) -∗ instr 0x15c9c (Some a15c9c) -∗
  instr 0x15ca0 (Some a15ca0) -∗ instr 0x15ca4 (Some a15ca4) -∗
  instr 0x15ca8 (Some a15ca8) -∗ instr 0x15cac (Some a15cac) -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c90
    (encoderBytesSuffixSpec data size sp ret bytes
      old_x6 old_s0 old_s1 stack2 tail P).
Proof.
  iStartProof. iIntros "#H90 #H94 #H98 #H9c #Ha0 #Ha4 #Ha8 #Hac #Houtput".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (encoder_bytes_suffix_correct with
    "H90 H94 H98 H9c Ha0 Ha4 Ha8 Hac Houtput").
Qed.
