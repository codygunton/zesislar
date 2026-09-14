Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.

Lemma array_byte_views_preserve_resources `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (i j : nat) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop i bytes)))) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop j bytes)))) ∗ P ∗ True)%I -∗
  (reg_col zesu_ram_sys_regs ∗ base ↦ₘ∗ bytes ∗
   "x16" ↦ᵣ RVal_Bits (bv_zero_extend 64 (default (BV 8 0) (bytes !! i))) ∗
   "x17" ↦ᵣ RVal_Bits (bv_zero_extend 64 (default (BV 8 0) (bytes !! j))) ∗ P ∗ True)%I.
Proof.
  iStartProof. iIntros "(Hsys & Hbytes & H16 & H17 & HP & _)".
  zesu_array_byte_register_views. iFrame.
Qed.
Print Assumptions array_byte_views_preserve_resources.

Lemma array_byte_view_outside bytes index :
  (length bytes <= index)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop index bytes))) = BV 64 0.
Proof.
  intros Hbound. rewrite array_byte_default (lookup_ge_None_2 _ _ Hbound).
  cbn. bv_solve.
Qed.
Print Assumptions array_byte_view_outside.

