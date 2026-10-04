Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Generated.TestTraces.LdX16X10Off80.

#[local] Instance stock_signed_address_rule : ZesuStepSignedAddress := I.


Import ZesuSsz.Automation.Hooks.

Lemma test_read_word_from_byte_array `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8)) :
  length bytes = 288%nat ->
  instr 0x800f163c (Some trace_ld_x16_x10_80) -∗
  instr_body 0x800f163c (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base ∧
      bv_unsigned base + 288 <= (machineRamEnd defaultMap)⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x800f1640 (
      reg_col zesu_sys_regs ∗
      "x10" ↦ᵣ RVal_Bits base ∗
      "x16" ↦ᵣ RVal_Bits
        (Z_to_bv 64
          (little_endian_to_bv 8 (take 8 (drop 80 bytes)))) ∗
      bv_unsigned base ↦ₘ∗ bytes ∗ True) ∗ True).
Proof.
  move => Hlength.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
Qed.

Print Assumptions test_read_word_from_byte_array.
