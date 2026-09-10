From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoundaries.

Definition encoderOptionalSomeAtPublicResume
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x1 old_x5 old_x6 old_x8 old_x10 old_x11 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits old_x1 ∗
    "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x6" ↦ᵣ RVal_Bits old_x6 ∗ "x8" ↦ᵣ RVal_Bits value ∗
    "x10" ↦ᵣ RVal_Bits old_x10 ∗
    "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 32) ↦ₘ? 16 ∗
    (bv_unsigned sp - 16) ↦ₘ old_x8 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeAfterBooleanEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtPublicResume) := I.

Definition encoderOptionalSomeAtPublicInt
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 old_x8 old_x11 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeAfterBooleanEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtPublicInt) := I.
