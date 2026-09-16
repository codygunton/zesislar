Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayPairViews.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.

Lemma array_pair_views_preserve_resources `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (low high : bv 8) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [low; high])) ∗ P ∗ True)%I -∗
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned low + bv_unsigned high * 256)) ∗ P ∗ True)%I.
Proof.
  iStartProof. iIntros "(Hsys & Hbytes & H14 & HP & _)".
  zesu_array_byte_pair_register_views. iFrame.
Qed.
Print Assumptions array_pair_views_preserve_resources.

