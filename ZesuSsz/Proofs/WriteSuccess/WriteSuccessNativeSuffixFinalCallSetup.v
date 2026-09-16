Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessPost159d4SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159d0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    (bv_unsigned sp + 88) ↦ₘ count ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost159d4SetupSpec) := I.

Definition writeSuccessPost159c8SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 88) ↦ₘ count ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp + 88 < (machineRamEnd defaultMap)⌝ ∗
    instr_pre 0x159d4 (writeSuccessPost159d4SetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost159c8SetupSpec) := I.

Lemma write_success_post_159c8_final_call_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x159c8 (writeSuccessPost159c8SetupSpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: iFrame.
  all: lazymatch goal with |- ?G => fail "final call setup residual" G end.
Qed.
