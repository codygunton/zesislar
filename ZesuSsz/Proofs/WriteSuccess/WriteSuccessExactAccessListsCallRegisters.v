Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_copy_call_registers `{!islaG Sigma} `{!threadG} (data : bv 64) :
  reg_col writeSuccessAccessListsOtherRegShapes -∗ "x10" ↦ᵣ RVal_Bits data -∗
  ∃ old_ra : bv 64, "x1" ↦ᵣ RVal_Bits old_ra ∗
    accessRegisterGroup ["x10"; "x12"; "x13"; "x14"; "x15"] ∗
    accessRegisterGroup ["x5"] ∗ accessRegisterGroup accessUnchangedRegisters ∗ True.
Proof.
  iIntros "Hregs Hdata".
  iDestruct (access_copy_register_groups with "Hregs") as
    (old_ra old5) "(Hra & H5 & Htmp & Hrest & _)".
  iExists old_ra. iFrame "Hra Hrest".
  iSplitL "Hdata Htmp".
  { unfold accessRegisterGroup. rewrite reg_col_cons.
    iSplitL "Hdata"; last (iExact "Htmp").
    iExists (RVal_Bits data). iFrame. done. }
  iSplitL "H5"; last done.
  iExists (RVal_Bits old5). iFrame. done.
Qed.
Print Assumptions access_copy_call_registers.
