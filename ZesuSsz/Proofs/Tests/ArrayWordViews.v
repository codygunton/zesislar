Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayWordViews.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.

Lemma array_word_views_preserve_resources `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (a b c d : bv 8) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a; b; c; d])) ∗ P ∗ True)%I -∗
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64
     (Z_to_bv 32 (little_endian_to_bv 8 [a; b; c; d]))) ∗ P ∗ True)%I.
Proof.
  iStartProof. iIntros "(Hsys & Hbytes & H14 & HP & _)".
  zesu_array_byte_four_register_views. iFrame.
Qed.
Print Assumptions array_word_views_preserve_resources.

