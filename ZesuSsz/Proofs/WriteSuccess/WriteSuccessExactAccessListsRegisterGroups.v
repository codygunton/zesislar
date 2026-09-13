Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Definition accessUnchangedRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9"; "x16"; "x17"; "x18";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"].
Definition accessRegisterGroup `{!islaG Sigma} `{!threadG}
    (registers : list string) : iProp Sigma :=
  reg_col ((λ register, (KindReg register, BitsShape 64)) <$> registers).
Global Instance : LithiumUnfold (@accessRegisterGroup) := I.

Lemma access_copy_register_groups `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessAccessListsOtherRegShapes -∗
  ∃ old_ra old5 : bv 64,
    "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
    accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗
    accessRegisterGroup accessUnchangedRegisters ∗ True.
Proof.
  iIntros "Hregs".
  iAssert (accessRegisterGroup ["x1"] ∗ accessRegisterGroup ["x5"] ∗
    accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗
    accessRegisterGroup accessUnchangedRegisters)%I with "[Hregs]" as "Hgroups".
  { unfold accessRegisterGroup, reg_col. rewrite -!big_sepL_app.
    iApply (big_sepL_submseteq with "Hregs").
    cbn [writeSuccessAccessListsOtherRegShapes writeSuccessAccessListsOtherRegisters
      accessUnchangedRegisters fmap]. solve_submseteq. }
  iDestruct "Hgroups" as "(Hra & H5 & Htmp & Hrest)".
  iEval (unfold accessRegisterGroup) in "Hra".
  iEval (unfold accessRegisterGroup) in "H5".
  iEval (rewrite reg_col_cons reg_col_nil) in "Hra".
  iEval (rewrite reg_col_cons reg_col_nil) in "H5".
  iDestruct "Hra" as "((%vra & %Hra & Hra) & _)".
  iDestruct "H5" as "((%v5 & %H5 & H5) & _)".
  destruct (valu_has_bits_shape _ _ Hra) as [old_ra ->].
  destruct (valu_has_bits_shape _ _ H5) as [old5 ->].
  iExists old_ra, old5. iFrame.
Qed.
Print Assumptions access_copy_register_groups.
