Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
From IslaTraces.write_success_00 Require Import a14d34.

Import ZesuSsz.Automation.Hooks.

Lemma test_write_word_to_byte_array `{!islaG Sigma} `{!threadG}
    (base value : bv 64) (bytes : list (bv 8)) :
  length bytes = 2048%nat ->
  instr 0x14d34 (Some a14d34) -∗
  instr_body 0x14d34 (
    reg_col zesu_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    "x1" ↦ᵣ RVal_Bits value ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base ∧
      bv_unsigned base + 2048 <= 0x40000000⌝ ∗
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
  have -> : bv_unsigned (base + 1992) - bv_unsigned base = 1992
    by bv_solve.
  done.
Qed.

Print Assumptions test_write_word_to_byte_array.
