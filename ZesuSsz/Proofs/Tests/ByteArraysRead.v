Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
From IslaTraces.write_success_32 Require Import a15048.

Import ZesuSsz.Automation.Hooks.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma test_read_word_from_byte_array `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8)) :
  length bytes = 288%nat ->
  instr 0x15048 (Some a15048) -∗
  instr_body 0x15048 (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base ∧
      bv_unsigned base + 288 <= 0x40000000⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x1504c (
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
  have -> : bv_unsigned (base + 80) - bv_unsigned base = 80 by bv_solve.
  done.
Qed.

Print Assumptions test_read_word_from_byte_array.
