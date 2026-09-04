From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsLoadBlock.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockCore.

Definition writeSuccessLoadBlockWithFrameSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
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
      writeSuccessLoadBlockStack sp values ∗
      bv_unsigned sp ↦ₘ? 8 ∗
      (bv_unsigned sp + 104) ↦ₘ? 176 ∗ True))%I.

Local Instance : LithiumUnfold (@writeSuccessLoadBlockWithFrameSpec) := I.

Lemma write_success_load_block_with_frame
    `{!islaG Sigma} `{!threadG} :
  instr_body_lookup_resources
    IslaTraces.write_success_blocks.Index.body_lookup -∗
  instr_body 0x14d80 writeSuccessLoadBlockWithFrameSpec.
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
  all: try (replace (bv_unsigned sp + 104) with
    (bv_unsigned sp + 96 + 8) by lia; iFrame).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
