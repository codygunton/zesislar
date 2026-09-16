Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessStorageKeysSpec WriteSuccessExactStorageKeysRegisterGroups
  WriteSuccessExactStorageKeysEmit.

Lemma storage_keys_return_registers `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (key : list (bv 8)) :
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x153a8) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1712)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   "x12" ↦ᵣ RVal_Bits (storageKeyWord key 8) ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyWord key 16) ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyWord key 0) ∗
   storageKeysRegisterBlock
     ["x24"; "x25"; "x26"; "x18"; "x23"; "x31"; "x30"; "x29";
      "x16"; "x8"; "x21"; "x20"; "x9"; "x7"; "x28";
      "x17"; "x6"; "x15"] ∗ storageKeysRegisterBlock ["x3"; "x4"] ∗ True)%I -∗
  reg_col writeSuccessStorageKeysOtherRegShapes.
Proof.
  iIntros "(H1 & H5 & H10 & H11 & H12 & H13 & H14 & Hother & Hgp & _)".
  iAssert (storageKeysRegisterBlock ["x1"; "x5"; "x10"; "x11"; "x12"; "x13"; "x14"])
    with "[H1 H5 H10 H11 H12 H13 H14]" as "Hknown".
  { unfold storageKeysRegisterBlock. cbn [fmap].
    rewrite !reg_col_cons reg_col_nil.
    iSplitL "H1". { iExists _. iFrame. done. }
    iSplitL "H5". { iExists _. iFrame. done. }
    iSplitL "H10". { iExists _. iFrame. done. }
    iSplitL "H11". { iExists _. iFrame. done. }
    iSplitL "H12". { iExists _. iFrame. done. }
    iSplitL "H13". { iExists _. iFrame. done. }
    iSplitL "H14". { iExists _. iFrame. done. } done. }
  iCombine "Hknown Hother Hgp" as "Hall".
  iEval (unfold storageKeysRegisterBlock, reg_col) in "Hall".
  iEval (rewrite -!big_sepL_app) in "Hall".
  unfold reg_col. iApply (big_sepL_submseteq with "Hall").
  cbn [writeSuccessStorageKeysOtherRegShapes writeSuccessStorageKeysOtherRegisters fmap].
  solve_submseteq.
Qed.
Print Assumptions storage_keys_return_registers.
