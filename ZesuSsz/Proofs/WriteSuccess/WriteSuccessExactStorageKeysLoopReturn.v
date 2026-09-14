Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessStorageKeysSpec WriteSuccessLoopCommon WriteSuccessExactStorageKeysModel
  WriteSuccessExactStorageKeysEmit WriteSuccessExactStorageKeysEmitHandoff
  WriteSuccessExactStorageKeysWords WriteSuccessExactStorageKeysLoopEntry
  WriteSuccessExactStorageKeysReturnRegisters WriteSuccessExactStorageKeysPayloadScratchAt
  WriteSuccessExactStorageKeysRegisterGroups WriteSuccessExactStorageKeysTail.

Definition storageKeysTailFrame `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessStorageKeysOtherRegShapes ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactStorageKeysEvents sp (S processed) remaining bytes tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysTailFrame) := I.

Lemma storage_keys_output_to_tail `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  storageKeysEmitPost sp (take 32 (drop (32 * processed) bytes))
    (writeSuccessExactStorageKeysEvents sp (S processed) remaining bytes tail)
    (storageKeysEmitCallerFrame pointer base bytes (32 * processed)
      (storageKeysLoopFrame x19 sp pointer base total processed remaining bytes tail P)) -∗
  storageKeysTailState pointer (Z_to_bv 64 (Z.of_nat (S remaining)))
    (storageKeysTailFrame x19 sp pointer base total processed remaining bytes tail P).
Proof.
  iIntros "Hpost".
  iEval (unfold storageKeysEmitPost, storageKeysEmitFrame,
    storageKeysEmitCallerFrame, storageKeysWordFrame, storageKeysLoopFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H5 & H10 & H11 & Hkey & Hmmio & Htrace & (Hsp & H12 & H13 & H14 & (Hother & (Hpointer & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & (Hgp & H19 & H27 & HP & Hinv & Hexit & _) & _) & _) & _) & _)".
  have Hkeylength : length (take 32 (drop (32 * processed) bytes)) = 32%nat.
  { rewrite length_take length_drop. lia. }
  iPoseProof (storage_keys_return_registers sp (take 32 (drop (32 * processed) bytes))
    with "[H1 H5 H10 H11 H12 H13 H14 Hother Hgp]") as "Hregs".
  { iFrame. }
  iEval (unfold writeSuccessFixedWidthArrayInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htotal & %Hlength & %Hposition & %Hcount & %Halign16 & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _)".
  iPoseProof (storage_keys_payload_scratch_at sp (take 32 (drop (32 * processed) bytes))
    Hsplow ltac:(clear Hcount; lia) Hkeylength with "Hkey") as "Hscratch".
  iEval (unfold storageKeysTailState, storageKeysTailFrame,
    writeSuccessFixedWidthArrayInvariant).
  iFrame. repeat iSplit; try (iPureIntro; assumption).
  done.
Qed.
Print Assumptions storage_keys_output_to_tail.
