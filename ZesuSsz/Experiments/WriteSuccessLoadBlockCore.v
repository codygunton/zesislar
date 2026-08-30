From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index Hints22 Hints23 Hints24.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.

Import ListNotations.

Definition writeSuccessLoadBlockModifiedRegisters : list string :=
  ["x10"; "x11"; "x12"; "x13"; "x14"].

Definition writeSuccessLoadBlockRegisterShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessLoadBlockModifiedRegisters.

Definition writeSuccessLoadBlockWord (values : list (bv 64)) (index : nat) :
    bv 64 := default (BV 64 0) (values !! index).

Definition writeSuccessLoadBlockResultRegisters
    (values : list (bv 64)) : list (reg_kind * valu_shape) := [
  (KindReg "x10", ExactShape (RVal_Bits (writeSuccessLoadBlockWord values 10)));
  (KindReg "x11", ExactShape (RVal_Bits (writeSuccessLoadBlockWord values 11)));
  (KindReg "x12", ExactShape (RVal_Bits (writeSuccessLoadBlockWord values 12)));
  (KindReg "x13", ExactShape (RVal_Bits (writeSuccessLoadBlockWord values 13)));
  (KindReg "x14", ExactShape (RVal_Bits (writeSuccessLoadBlockWord values 15)))
].

Definition writeSuccessLoadBlockStack `{!islaG Sigma} (sp : bv 64)
    (values : list (bv 64)) : iProp Sigma :=
  (bv_unsigned sp + 24) ↦ₘ (writeSuccessLoadBlockWord values 0) ∗
  (bv_unsigned sp + 16) ↦ₘ (writeSuccessLoadBlockWord values 1) ∗
  (bv_unsigned sp + 40) ↦ₘ (writeSuccessLoadBlockWord values 2) ∗
  (bv_unsigned sp + 32) ↦ₘ (writeSuccessLoadBlockWord values 3) ∗
  (bv_unsigned sp + 56) ↦ₘ (writeSuccessLoadBlockWord values 4) ∗
  (bv_unsigned sp + 48) ↦ₘ (writeSuccessLoadBlockWord values 5) ∗
  (bv_unsigned sp + 64) ↦ₘ (writeSuccessLoadBlockWord values 6) ∗
  (bv_unsigned sp + 72) ↦ₘ (writeSuccessLoadBlockWord values 7) ∗
  (bv_unsigned sp + 8) ↦ₘ (writeSuccessLoadBlockWord values 8) ∗
  (bv_unsigned sp + 80) ↦ₘ (writeSuccessLoadBlockWord values 9) ∗
  (bv_unsigned sp + 296) ↦ₘ (writeSuccessLoadBlockWord values 10) ∗
  (bv_unsigned sp + 304) ↦ₘ (writeSuccessLoadBlockWord values 11) ∗
  (bv_unsigned sp + 280) ↦ₘ (writeSuccessLoadBlockWord values 12) ∗
  (bv_unsigned sp + 288) ↦ₘ (writeSuccessLoadBlockWord values 13) ∗
  (bv_unsigned sp + 96) ↦ₘ (writeSuccessLoadBlockWord values 14) ∗
  (bv_unsigned sp + 88) ↦ₘ (writeSuccessLoadBlockWord values 15).

Local Instance : LithiumUnfold (@writeSuccessLoadBlockStack) := I.

Definition writeSuccessLoadBlockSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp base : bv 64) (values : list (bv 64)),
    reg_col zesu_instr_sys_regs ∗
    reg_col writeSuccessLoadBlockRegisterShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 720) ↦ₘ∗ values ∗
    bv_unsigned sp ↦ₘ? 312 ∗
    ⌜length values = 16%nat⌝ ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base + 720⌝ ∗
    ⌜bv_unsigned base + 848 < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
    instr_pre 0x14e00 (
      reg_col zesu_instr_sys_regs ∗
      reg_col (writeSuccessLoadBlockResultRegisters values) ∗
      "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
      (bv_unsigned base + 720) ↦ₘ∗ values ∗
      writeSuccessLoadBlockStack sp values ∗ True))%I.

Local Instance : LithiumUnfold (@writeSuccessLoadBlockSpec) := I.

Lemma write_success_load_block_correct `{!islaG Sigma} `{!threadG} :
  instr_body_lookup_resources
    IslaTraces.write_success_blocks.Index.body_lookup -∗
  instr_body 0x14d80 writeSuccessLoadBlockSpec.
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; lia).
  all: try bv_solve.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; lia).
  all: try bv_solve.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Global Opaque writeSuccessLoadBlockSpec.

Lemma write_success_load_block_pre `{!islaG Sigma} `{!threadG} :
  instr_body_lookup_resources
    IslaTraces.write_success_blocks.Index.body_lookup -∗
  □ instr_pre 0x14d80 writeSuccessLoadBlockSpec.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply write_success_load_block_correct. iExact "Hcode".
Qed.
