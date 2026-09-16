Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import isla.riscv64.riscv64.

Lemma storage_registers_access_return `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessStorageKeysOtherRegShapes -∗
  ∃ data index : bv 64, reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits index ∗ True.
Proof.
  iIntros "Hregs".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
    reg_col writeSuccessAccessListsOtherRegShapes)%I with "[Hregs]" as "[Hdata Hregs]".
  { unfold reg_col. rewrite -big_sepL_app.
    iApply (big_sepL_submseteq with "Hregs").
    cbn [writeSuccessStorageKeysOtherRegShapes writeSuccessStorageKeysOtherRegisters
      writeSuccessAccessListsOtherRegShapes writeSuccessAccessListsOtherRegisters fmap].
    solve_submseteq. }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hdata".
  iDestruct "Hdata" as "((%vdata & %Hdata & Hdata) & (%vindex & %Hindex & Hindex) & _)".
  destruct (valu_has_bits_shape _ _ Hdata) as [data ->].
  destruct (valu_has_bits_shape _ _ Hindex) as [index ->].
  iExists data, index. iFrame.
Qed.
Print Assumptions storage_registers_access_return.
