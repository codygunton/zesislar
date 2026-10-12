Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.

Lemma decodeItemMaskedReturnAddress (ret : bv 64) :
  bv_extract 0 1 ret = BV 1 0 ->
  bv_unsigned (bv_or (bv_and ret (BV 64 18446744073709551614)) (BV 64 0)) =
    bv_unsigned ret.
Proof.
  intros Haligned.
  pose proof (normalize_instr_addr_riscv64_ret_tac ret _ Haligned eq_refl) as Hmasked.
  assert (Hzero : bv_add ret (BV 64 0) = ret) by bv_solve.
  rewrite !bv_wrap_bv_unsigned Hzero in Hmasked. exact Hmasked.
Qed.

#[export] Instance decodeItemMaskedReturnDerivedFacts (ret : bv 64) :
  ZesuDerivedFacts (bv_extract 0 1 ret = BV 1 0)
    (bv_unsigned (bv_or (bv_and ret (BV 64 18446744073709551614)) (BV 64 0)) =
      bv_unsigned ret).
Proof. exact (decodeItemMaskedReturnAddress ret). Qed.

Print Assumptions decodeItemMaskedReturnAddress.
Print Assumptions decodeItemMaskedReturnDerivedFacts.
