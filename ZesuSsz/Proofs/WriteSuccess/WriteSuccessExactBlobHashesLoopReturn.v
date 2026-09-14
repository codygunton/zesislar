Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessLoopCommon WriteSuccessExactBlobHashesModel
  WriteSuccessExactBlobHashesEmit WriteSuccessExactBlobHashesEmitHandoff
  WriteSuccessExactBlobHashesWide WriteSuccessExactBlobHashesLoopEntry
  WriteSuccessExactBlobHashesReturnRegisters WriteSuccessExactBlobHashesPayloadScratch
  WriteSuccessExactBlobHashesTail.

Definition blobTailFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col (list_delete 19%nat writeSuccessBlobHashesBodyOtherRegShapes) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (writeSuccessExactBlobHashesEvents sp (S processed) remaining bytes tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@blobTailFrame) := I.

Lemma blob_output_to_tail `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  blobEmitPost sp (take 32 (drop (32 * processed) bytes)) (writeSuccessExactBlobHashesEvents sp (S processed) remaining bytes tail)
    (blobEmitCallerFrame pointer (Z_to_bv 64 (Z.of_nat (S remaining))) base bytes (32 * processed)
      (blobLoopFrame sp pointer base total processed remaining bytes tail P)) -∗
  ∃ value22 : bv 64, blobTailState pointer (Z_to_bv 64 (Z.of_nat (S remaining))) value22
    (blobTailFrame sp pointer base total processed remaining bytes tail P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobEmitPost, blobEmitFrame, blobEmitCallerFrame, blobWordFrame,
    blobLoopFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H5 & H10 & H11 & Hkey & Hmmio & Htrace &
      (Hsp & H12 & H13 & H14 & (Hother & (Hpointer & Hcountreg & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh &
        (Hgp & HP & Hinv & Hexit & _) & _) & _) & _) & _)".
  have Hkeylength : length (take 32 (drop (32 * processed) bytes)) = 32%nat.
  { rewrite length_take length_drop. lia. }
  iPoseProof (blob_return_registers sp (take 32 (drop (32 * processed) bytes))
    with "[H1 H5 H10 H11 H12 H13 H14 Hother Hgp]") as "Hregs".
  { iFrame. }
  iDestruct (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 19 (KindReg "x22", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (value Hshape) "(H22 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hshape) as [value22 ->].
  iEval (unfold writeSuccessFixedWidthArrayInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htotal & %Hlength & %Hposition & %Hcount & %Halign16 & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _)".
  iPoseProof (blob_payload_scratch_at sp (take 32 (drop (32 * processed) bytes))
    Hsplow ltac:(clear Hcount; lia) Hkeylength with "Hkey") as "Hscratch".
  iExists value22.
  iEval (unfold blobTailState, blobTailFrame, writeSuccessFixedWidthArrayInvariant).
  iFrame. repeat iSplit; try (iPureIntro; assumption). done.
Qed.
Print Assumptions blob_output_to_tail.
