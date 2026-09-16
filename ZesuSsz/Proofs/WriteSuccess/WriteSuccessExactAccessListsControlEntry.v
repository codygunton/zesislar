Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControl.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessControlScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (storedIndex savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   writeSuccessStorageKeysScratch sp ∗ True)%I.
Global Instance : LithiumUnfold (@accessControlScratch) := I.

Definition accessControlFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessAccessListsOtherRegShapes ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   accessControlScratch sp base storedIndex savedX22 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAccessListsEvents sp remaining tail) ∗
   ⌜entries = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@accessControlFrame) := I.


Lemma access_control_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 x10 x22 x27 tail
    (P : iProp Sigma) :
  writeSuccessExactAccessListsState sp base entries processed remaining bytes
    storedIndex x19 savedX22 x10 x22 x27 tail P -∗
  accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries)))
    (Z_to_bv 64 (Z.of_nat (length processed))) x10
    (accessControlFrame sp base entries processed remaining bytes
      storedIndex x19 savedX22 x10 x22 x27 tail P).
Proof.
  iIntros "(Hsys & Hregs & Hsp & H19 & Hdata & Hcursor & H22 & H27 &
    Hbytes & Hown & Hscratch & Hmmio & Htrace & Hpartition & Hencoding & Hlength &
    Hcount & %Halign & %Hlow & %Hhigh & Hbaselow & Hbasehigh & HP & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hcopy & Hstack & Hkeys & _)".
  unfold accessListsControlState. iFrame "Hsys Hsp Hdata Hcursor Htotal".
  iSplit; first (iPureIntro; apply stack_align8_from16; assumption).
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro; lia).
  unfold accessControlFrame, accessControlScratch. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions access_control_entry_resources.
