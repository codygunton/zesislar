Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessExactAccessListsRegisterGroups.

Lemma access_blob_registers `{!islaG Sigma} `{!threadG} (sp old27 : bv 64) :
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x153d0) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   "x27" ↦ᵣ RVal_Bits old27 ∗ accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗
   accessRegisterGroup accessUnchangedRegisters ∗ True)%I -∗
  reg_col writeSuccessBlobHashesOtherRegShapes.
Proof.
  iIntros "(H1 & H5 & H10 & H11 & H27 & Htmp & Hother & _)".
  iAssert (accessRegisterGroup ["x1"; "x5"; "x10"; "x11"; "x27"])
    with "[H1 H5 H10 H11 H27]" as "Hknown".
  { unfold accessRegisterGroup. cbn [fmap]. rewrite !reg_col_cons reg_col_nil.
    iSplitL "H1". { iExists _. iFrame. done. }
    iSplitL "H5". { iExists _. iFrame. done. }
    iSplitL "H10". { iExists _. iFrame. done. }
    iSplitL "H11". { iExists _. iFrame. done. }
    iSplitL "H27". { iExists _. iFrame. done. } done. }
  iCombine "Hknown Htmp Hother" as "Hall".
  iEval (unfold accessRegisterGroup, reg_col; rewrite -!big_sepL_app) in "Hall".
  unfold reg_col. iApply (big_sepL_submseteq with "Hall").
  cbn [writeSuccessBlobHashesOtherRegShapes writeSuccessBlobHashesOtherRegisters accessUnchangedRegisters fmap].
  solve_submseteq.
Qed.
Print Assumptions access_blob_registers.
