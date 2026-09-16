Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessPost1594cSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15948) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    (bv_unsigned sp + 40) ↦ₘ pointer ∗
    (bv_unsigned sp + 32) ↦ₘ count ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost1594cSetupSpec) := I.

Definition writeSuccessPost15940SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 40) ↦ₘ pointer ∗
    (bv_unsigned sp + 32) ↦ₘ count ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp + 32⌝ ∗
    ⌜bv_unsigned sp + 40 < (machineRamEnd defaultMap)⌝ ∗
    instr_pre 0x1594c (writeSuccessPost1594cSetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost15940SetupSpec) := I.

Lemma write_success_post_15940_byte_list_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15940 (writeSuccessPost15940SetupSpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15940 setup residual" G end.
Qed.

Definition writeSuccessPost1595cSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15958) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    (bv_unsigned sp + 56) ↦ₘ pointer ∗
    (bv_unsigned sp + 48) ↦ₘ count ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost1595cSetupSpec) := I.

Definition writeSuccessPost15950SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 56) ↦ₘ pointer ∗
    (bv_unsigned sp + 48) ↦ₘ count ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp + 48⌝ ∗
    ⌜bv_unsigned sp + 56 < (machineRamEnd defaultMap)⌝ ∗
    instr_pre 0x1595c (writeSuccessPost1595cSetupSpec P) ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessPost15950SetupSpec) := I.

Lemma write_success_post_15950_byte_list_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15950 (writeSuccessPost15950SetupSpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "15950 setup residual" G end.
Qed.
