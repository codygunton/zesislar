Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
From IslaTraces.write_success_00 Require Import a14d34.

Import ZesuSsz.Automation.Hooks.

#[local] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.

Lemma test_write_word_to_byte_array `{!islaG Sigma} `{!threadG}
    (base value : bv 64) (bytes : list (bv 8)) :
  length bytes = 2048%nat ->
  instr 0x14d34 (Some a14d34) -∗
  instr_body 0x14d34 (
    reg_col zesu_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    "x1" ↦ᵣ RVal_Bits value ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base ∧
      bv_unsigned base + 2048 <= (machineRamEnd defaultMap)⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x14d38 (
      reg_col zesu_sys_regs ∗
      "x2" ↦ᵣ RVal_Bits base ∗
      "x1" ↦ᵣ RVal_Bits value ∗
      bv_unsigned base ↦ₘ∗
        (take 1992 bytes ++
         bv_to_little_endian 8 8 (bv_unsigned value) ++
         drop 2000 bytes) ∗ True) ∗ True).
Proof.
  move => Hlength.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
Qed.

Print Assumptions test_write_word_to_byte_array.
