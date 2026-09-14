Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageOwnReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessTailLoopScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat) (savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   writeSuccessStorageKeysScratch sp ∗ True)%I.
Global Instance : LithiumUnfold (@accessTailLoopScratch) := I.

Definition accessTailLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (x19 savedX22 data pointer : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessAccessListsOtherRegShapes ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x22" ↦ᵣ RVal_Bits pointer ∗ "x27" ↦ᵣ RVal_Bits (BV 64 0) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   accessTailLoopScratch sp base (length entries) savedX22 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (writeSuccessExactAccessListsEvents sp remaining tail) ∗
   ⌜entries = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessTailLoopFrame) := I.

Lemma access_tail_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes x19 savedX22 tail (P : iProp Sigma) :
  writeSuccessStorageKeysLoopExit x19 sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P) -∗
  ∃ data old11 pointer : bv 64,
    accessListsTailEntry sp (Z_to_bv 64 (Z.of_nat (length processed))) old11
      (accessTailLoopFrame sp base entries (processed ++ [entry]) rest bytes x19 savedX22
        data pointer tail P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as (pointer)
    "(Hsys & Hregs & H19 & Hsp & Hptr & Hcount & Hkeys & Hkeyscratch & Hmmio & Htrace & Hframe & %Hfinal & _)".
  iDestruct "Hframe" as "(Hbytes & Hprocessed & Hrest & %Hvalid & %Hkeylow & %Hkeyhigh &
    Hcopied & Hsaved & Hbase & Htotal & Hindex & Hstack & %Hpartition & Hencoding & Hlength &
    Htotalbound & %Halign & %Hlow & %Hhigh & Hbaselow & Hbasehigh & HP & _)".
  iDestruct (storage_registers_access_return with "Hregs") as (data old11)
    "(Hregs & Hdata & H11 & _)".
  iAssert (writeSuccessAccessEntriesOwn entries) with "[Hkeys Hprocessed Hrest]" as "Hown".
  { iApply (access_storage_ownership_return entries processed entry rest). iFrame.
    repeat iSplit; try done; iPureIntro; unfold writeSuccessAccessEntryValid in Hvalid; tauto. }
  iPoseProof (byte_array_forget with "Hcopied") as "Hcopied".
  iEval (rewrite (proj1 Hvalid)) in "Hcopied".
  have Hpartition' : entries = (processed ++ [entry]) ++ rest.
  { rewrite -app_assoc /=. exact Hpartition. }
  iExists data, old11, pointer. unfold accessListsTailEntry.
  iFrame "Hsys Hsp H11 Hindex".
  iSplit; first (iPureIntro; exact (stack_align8_from16 sp Halign)).
  iSplit; first (iPureIntro; clear -Hlow; lia).
  iSplit; first (iPureIntro; clear -Hhigh; lia).
  unfold accessTailLoopFrame, accessTailLoopScratch. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions access_tail_loop_entry_resources.
