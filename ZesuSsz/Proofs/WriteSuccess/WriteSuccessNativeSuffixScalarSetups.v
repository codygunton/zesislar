Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessSuffixInt15968SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15964) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits value ∗ (bv_unsigned sp + 64) ↦ₘ value ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15968SetupSpec) := I.

Definition writeSuccessSuffixInt15960SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 64) ↦ₘ value ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 64 < 0x40000000⌝ ∗
    instr_pre 0x15968 (writeSuccessSuffixInt15968SetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15960SetupSpec) := I.

Lemma write_success_suffix_int_15960_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15960 (writeSuccessSuffixInt15960SetupSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15960 setup residual" G end.
Qed.

Definition writeSuccessSuffixBooleanSetupTarget
    `{!islaG Sigma} `{!threadG} (returnBase value : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits returnBase ∗
   "x10" ↦ᵣ RVal_Bits value ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBooleanSetupTarget) := I.

Definition writeSuccessSuffixBooleanSetupEntry
    `{!islaG Sigma} `{!threadG} (target : Z) (returnBase value : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   instr_pre target (writeSuccessSuffixBooleanSetupTarget returnBase value P) ∗
   P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBooleanSetupEntry) := I.

Lemma write_success_suffix_boolean_15974_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15974
    (writeSuccessSuffixBooleanSetupEntry 0x1597c
      (BV 64 0x15978) (BV 64 1) P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15974 setup residual" G end.
Qed.

Lemma write_success_suffix_boolean_15994_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15994
    (writeSuccessSuffixBooleanSetupEntry 0x1599c
      (BV 64 0x15998) (BV 64 0) P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15994 setup residual" G end.
Qed.

Definition writeSuccessSuffixBytes1598cSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15988) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗ (bv_unsigned sp + 8) ↦ₘ count ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes1598cSetupSpec) := I.

Definition writeSuccessSuffixBytes15980SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 8) ↦ₘ count ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 8 < 0x40000000⌝ ∗
    instr_pre 0x1598c (writeSuccessSuffixBytes1598cSetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes15980SetupSpec) := I.

Lemma write_success_suffix_bytes_15980_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15980 (writeSuccessSuffixBytes15980SetupSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15980 setup residual" G end.
Qed.

Definition writeSuccessSuffixInt159acSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp saved value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159a8) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits saved ∗ "x10" ↦ᵣ RVal_Bits value ∗
    (bv_unsigned sp + 96) ↦ₘ saved ∗ (bv_unsigned sp + 80) ↦ₘ value ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159acSetupSpec) := I.

Definition writeSuccessSuffixInt159a0SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp saved value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 96) ↦ₘ saved ∗ (bv_unsigned sp + 80) ↦ₘ value ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 80⌝ ∗
    ⌜bv_unsigned sp + 96 < 0x40000000⌝ ∗
    instr_pre 0x159ac (writeSuccessSuffixInt159acSetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159a0SetupSpec) := I.

Lemma write_success_suffix_int_159a0_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x159a0 (writeSuccessSuffixInt159a0SetupSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "159a0 setup residual" G end.
Qed.

Definition writeSuccessSuffixJump15990Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ instr_pre 0x159a0 P ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixJump15990Spec) := I.

Lemma write_success_suffix_jump_15990
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15990 (writeSuccessSuffixJump15990Spec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15990 jump residual" G end.
Qed.
