Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysRegisterGroups.

Definition blobRegisterGroups `{!islaG Sigma} `{!threadG}
    (old26 : bv 64) : iProp Sigma :=
  (storageKeysRegisterBlock ["x6"; "x7"; "x28"; "x8"] ∗
   storageKeysRegisterBlock ["x9"; "x18"; "x20"; "x21"] ∗
   storageKeysRegisterBlock ["x10"; "x14"; "x13"; "x12"] ∗
   storageKeysRegisterBlock ["x11"; "x5"; "x17"; "x16"] ∗
   storageKeysRegisterBlock ["x15"; "x31"; "x30"; "x29"] ∗
   storageKeysRegisterBlock ["x27"; "x23"; "x24"] ∗
   storageKeysRegisterBlock ["x25"; "x1"] ∗
   "x26" ↦ᵣ RVal_Bits old26 ∗ storageKeysRegisterBlock ["x3"; "x4"] ∗ True)%I.
Global Instance : LithiumUnfold (@blobRegisterGroups) := I.

Lemma blob_register_groups `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessBlobHashesOtherRegShapes -∗
  ∃ old26 : bv 64, blobRegisterGroups old26.
Proof.
  iIntros "Hregs".
  iAssert (storageKeysRegisterBlock ["x6"; "x7"; "x28"; "x8"] ∗
   storageKeysRegisterBlock ["x9"; "x18"; "x20"; "x21"] ∗
   storageKeysRegisterBlock ["x10"; "x14"; "x13"; "x12"] ∗
   storageKeysRegisterBlock ["x11"; "x5"; "x17"; "x16"] ∗
   storageKeysRegisterBlock ["x15"; "x31"; "x30"; "x29"] ∗
   storageKeysRegisterBlock ["x27"; "x23"; "x24"] ∗
   storageKeysRegisterBlock ["x25"; "x1"] ∗
   storageKeysRegisterBlock ["x26"] ∗
   storageKeysRegisterBlock ["x3"; "x4"])%I with "[Hregs]" as "Hgroups".
  { unfold storageKeysRegisterBlock, reg_col. rewrite -!big_sepL_app.
    iApply (big_sepL_submseteq with "Hregs").
    cbn [writeSuccessBlobHashesOtherRegShapes writeSuccessBlobHashesOtherRegisters fmap].
    solve_submseteq. }
  iDestruct "Hgroups" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H26 & Hgp)".
  iEval (unfold storageKeysRegisterBlock) in "H26".
  iEval (rewrite reg_col_cons reg_col_nil) in "H26".
  iDestruct "H26" as "((%value & %Hshape & H26) & _)".
  destruct (valu_has_bits_shape _ _ Hshape) as [old26 ->].
  iExists old26. iEval (unfold blobRegisterGroups). iFrame.
Qed.
Print Assumptions blob_register_groups.
