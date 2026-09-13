Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessLoopCommon WriteSuccessExactBlobHashesModel
  WriteSuccessExactBlobHashesLoads16 WriteSuccessExactBlobHashesLoadHandoff
  WriteSuccessExactBlobHashesUpperLoadHandoff WriteSuccessExactBlobHashesLowerLoadHandoff
  WriteSuccessExactBlobHashesInitialLoads WriteSuccessExactBlobHashesEmitHandoff
  WriteSuccessExactBlobHashesRegisterGroups WriteSuccessExactStorageKeysRegisterGroups.

Definition blobLoopFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (storageKeysRegisterBlock ["x3"; "x4"] ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoopFrame) := I.

Lemma blob_loop_entry_resources `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessBlobHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactBlobHashesEvents sp processed (S remaining) bytes tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I -∗
  ∃ old26 a b c d : bv 64,
    blobLoads16Entry pointer base bytes (32 * processed)
      (blobLoad20Frame bytes (32 * processed)
        (blobUpperLoadFrame (Z_to_bv 64 (Z.of_nat (S remaining))) bytes (32 * processed)
          (⌜(32 * processed + 32 <= length bytes)%nat⌝ ∗
           reg_col [(KindReg "x25", BitsShape 64)] ∗
           ("x26" ↦ᵣ RVal_Bits old26 ∗
            blobOutputResources sp a b c d (take 32 (drop (32 * processed) bytes))
              (writeSuccessExactBlobHashesEvents sp (S processed) remaining bytes tail) (blobLoopFrame sp pointer base total processed remaining bytes tail P) ∗ True) ∗ True)%I)).
Proof.
  iIntros "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Hregs & Hsp & Hpointer & Hcountreg & Harray & Hscratch & Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessFixedWidthArrayInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htotal & %Hlength & %Hcursor & %Hcount & %Halign16 & %Hsplow & %Hsphigh & %Hlow & %Hhigh & _)".
  have Halign8 : bv_unsigned sp `mod` 8 = 0 by apply stack_align8_from16.
  iDestruct (blob_register_groups with "Hregs") as (old26) "Hgroups".
  iEval (unfold blobRegisterGroups) in "Hgroups".
  iDestruct "Hgroups" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H26 & Hgp & _)".
  iAssert (reg_col [(KindReg "x25", BitsShape 64)] ∗
    reg_col [(KindReg "x1", BitsShape 64)])%I with "[H7]" as "[H25 Hra]".
  { iEval (unfold storageKeysRegisterBlock, reg_col) in "H7".
    unfold reg_col. rewrite -big_sepL_app. iExact "H7". }
  iEval (unfold writeSuccessBlobHashesScratch) in "Hscratch".
  iDestruct "Hscratch" as (a b c d) "(Ha & Hb & Hc & Hd & _)".
  iEval (rewrite writeSuccessExactBlobHashesEvents_cons) in "Htrace".
  iExists old26, a, b, c, d.
  iEval (unfold blobLoads16Entry, blobLoad20Frame, blobUpperLoadFrame,
    blobLoad24Frame, blobLowerLoadFrame, blobLoad12Frame, blobOutputResources,
    blobLoopFrame, writeSuccessFixedWidthArrayInvariant, storageKeysRegisterBlock).
  iEval (unfold storageKeysRegisterBlock) in "H1 H2 H3 H4 H5 H6 Hgp".
  iFrame. repeat iSplit; try (iPureIntro; first [assumption | clear Hcount; lia]).
Qed.
Print Assumptions blob_loop_entry_resources.
