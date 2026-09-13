Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.

Definition storageKeysRegisterBlock `{!islaG Sigma} `{!threadG}
    (registers : list string) : iProp Sigma :=
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> registers).
Global Instance : LithiumUnfold (@storageKeysRegisterBlock) := I.

Definition storageKeysRegisterGroups `{!islaG Sigma} `{!threadG}
    (old21 : bv 64) : iProp Sigma :=
  (storageKeysRegisterBlock ["x6"; "x7"; "x28"; "x1"] ∗
   storageKeysRegisterBlock ["x8"; "x26"; "x9"; "x25"] ∗
   storageKeysRegisterBlock ["x10"; "x14"; "x13"; "x12"] ∗
   storageKeysRegisterBlock ["x11"; "x5"; "x17"; "x16"] ∗
   storageKeysRegisterBlock ["x15"; "x31"; "x30"; "x29"] ∗
   storageKeysRegisterBlock ["x24"; "x20"; "x18"; "x23"] ∗
   "x21" ↦ᵣ RVal_Bits old21 ∗ storageKeysRegisterBlock ["x3"; "x4"] ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysRegisterGroups) := I.

Lemma storage_keys_register_groups `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessStorageKeysOtherRegShapes -∗
  ∃ old21 : bv 64, storageKeysRegisterGroups old21.
Proof.
  iIntros "Hregs".
  iAssert (storageKeysRegisterBlock ["x6"; "x7"; "x28"; "x1"] ∗
    storageKeysRegisterBlock ["x8"; "x26"; "x9"; "x25"] ∗
    storageKeysRegisterBlock ["x10"; "x14"; "x13"; "x12"] ∗
    storageKeysRegisterBlock ["x11"; "x5"; "x17"; "x16"] ∗
    storageKeysRegisterBlock ["x15"; "x31"; "x30"; "x29"] ∗
    storageKeysRegisterBlock ["x24"; "x20"; "x18"; "x23"] ∗
    storageKeysRegisterBlock ["x21"] ∗ storageKeysRegisterBlock ["x3"; "x4"])%I
    with "[Hregs]" as "Hgroups".
  { unfold storageKeysRegisterBlock, reg_col.
    rewrite -!big_sepL_app.
    iApply (big_sepL_submseteq with "Hregs").
    cbn [writeSuccessStorageKeysOtherRegShapes writeSuccessStorageKeysOtherRegisters fmap].
    solve_submseteq. }
  iDestruct "Hgroups" as "(H1 & H2 & H3 & H4 & H5 & H6 & H21 & Hgp)".
  iEval (unfold storageKeysRegisterBlock) in "H21".
  iEval (rewrite reg_col_cons reg_col_nil) in "H21".
  iDestruct "H21" as "((%value & %Hshape & H21) & _)".
  destruct (valu_has_bits_shape _ _ Hshape) as [old21 ->].
  iExists old21. iEval (unfold storageKeysRegisterGroups). iFrame.
Qed.
Print Assumptions storage_keys_register_groups.
