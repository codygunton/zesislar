Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
From IslaTraces.write_success_32 Require Import a15048.

Import ZesuSsz.Automation.Hooks.

#[local] Hint Rewrite zesu_bv_sign_extend_same : isla_coq_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.

Lemma test_zesu_block `{!islaG Sigma} `{!threadG}
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
  zesu_block.
Qed.

Print Assumptions test_zesu_block.

Lemma test_zesu_pack `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  P -∗ ∃ n : nat, ⌜n = 7%nat⌝ ∗ P.
Proof.
  iStartProof. iIntros "HP". zesu_pack 7%nat.
Qed.

Print Assumptions test_zesu_pack.
