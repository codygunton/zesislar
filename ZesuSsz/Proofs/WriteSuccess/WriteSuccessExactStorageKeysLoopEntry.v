Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessStorageKeysSpec WriteSuccessLoopCommon WriteSuccessExactStorageKeysModel
  WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysLoadHandoff
  WriteSuccessExactStorageKeysUpperLoadHandoff WriteSuccessExactStorageKeysLowerLoadHandoff
  WriteSuccessExactStorageKeysInitialLoads WriteSuccessExactStorageKeysEmitHandoff
  WriteSuccessExactStorageKeysRegisterGroups.

Definition storageKeysLoopFrame `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (storageKeysRegisterBlock ["x3"; "x4"] ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoopFrame) := I.

Lemma storage_keys_loop_entry_resources `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessStorageKeysOtherRegShapes ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactStorageKeysEvents sp processed (S remaining) bytes tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True)%I -∗
  ∃ old21 a b c d : bv 64,
    storageKeysLoads16Entry pointer base bytes (32 * processed)
      (storageKeysLoad20Frame bytes (32 * processed)
        (storageKeysUpperLoadFrame bytes (32 * processed)
          (⌜(32 * processed + 32 <= length bytes)%nat⌝ ∗
            ("x21" ↦ᵣ RVal_Bits old21 ∗
             storageKeysOutputResources sp a b c d (take 32 (drop (32 * processed) bytes))
               (writeSuccessExactStorageKeysEvents sp (S processed) remaining bytes tail)
               (storageKeysLoopFrame x19 sp pointer base total processed remaining bytes tail P) ∗
             True) ∗ True)%I)).
Proof.
  iIntros "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Hregs & H19 & Hsp & Hpointer & H27 & Harray & Hscratch & Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessFixedWidthArrayInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htotal & %Hlength & %Hcursor & %Hcount & %Halign16 & %Hsplow & %Hsphigh & %Hlow & %Hhigh & _)".
  have Halign8 : bv_unsigned sp `mod` 8 = 0 by apply stack_align8_from16.
  iDestruct (storage_keys_register_groups with "Hregs") as (old21) "Hgroups".
  iEval (unfold storageKeysRegisterGroups) in "Hgroups".
  iDestruct "Hgroups" as "(H1 & H2 & H3 & H4 & H5 & H6 & H21 & Hgp & _)".
  iEval (unfold writeSuccessStorageKeysScratch) in "Hscratch".
  iDestruct "Hscratch" as (a b c d) "(Ha & Hb & Hc & Hd & _)".
  iEval (rewrite writeSuccessExactStorageKeysEvents_cons) in "Htrace".
  iExists old21, a, b, c, d.
  iEval (unfold storageKeysLoads16Entry, storageKeysLoad20Frame,
    storageKeysUpperLoadFrame, storageKeysLoad24Frame, storageKeysLowerLoadFrame,
    storageKeysLoad12Frame, storageKeysOutputResources, storageKeysLoopFrame,
    writeSuccessFixedWidthArrayInvariant, storageKeysRegisterBlock).
  iEval (unfold storageKeysRegisterBlock) in "H1 H2 H3 H4 H5 H6 Hgp".
  iFrame. repeat iSplit; try (iPureIntro; first [assumption | clear Hcount; lia]).
Qed.
Print Assumptions storage_keys_loop_entry_resources.
