Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsEntryValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsValidity.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessEntryAfterCountEvents (sp : bv 64) (entry : writeSuccessAccessEntry)
    (rest : list writeSuccessAccessEntry) (tail : spec) : spec :=
  writeSuccessExactStorageKeysEvents sp 0 (writeSuccessAccessEntryStorageCount entry)
    (writeSuccessAccessEntryStorageBytes entry) (writeSuccessExactAccessListsEvents sp rest tail).

Definition accessCountLoopScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total processed : nat) (savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 272) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   writeSuccessStorageKeysScratch sp ∗ True)%I.
Global Instance : LithiumUnfold (@accessCountLoopScratch) := I.

Definition accessCountLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗ accessRegisterGroup accessUnchangedRegisters ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   accessCountLoopScratch sp base (length entries) (length processed) savedX22 ∗
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
Global Instance : LithiumUnfold (@accessCountLoopFrame) := I.

Lemma access_count_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  (accessListsWholeOutputPost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterAddressEvents sp entry rest tail)
    (accessOutputLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P) ∗
   instr_pre 0x1521c (accessCountWholePost sp (writeSuccessAccessEntryBytes entry)
     (accessEntryAfterCountEvents sp entry rest tail)
     (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
       (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)) ∗ True)%I -∗
  accessCountWholeEntry sp (BV 64 0x15210) (BV 64 (mapIoContextAddress defaultMap))
    (sp + BV 64 1760)%bv (BV 64 20) (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P).
Proof.
  iIntros "(Hpost & Hnext & _)". iDestruct "Hpost" as
    "(Hsys & Hra & H5 & Hdata & Hsize & Hcopied & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & Hframe & _)".
  iDestruct "Hframe" as "(Htmp & Hrest & H19 & H22 & H27 & Hbytes & Hown & Hscratch &
    %Hpartition & %Hencoding & %Hlength & Hcount & %Halign & %Hlow & %Hhigh &
    %Hbaselow & %Hbasehigh & HP & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hstack & Hkeys & _)".
  iDestruct (access_entries_validity with "Hown") as "[%Hall Hown]".
  rewrite Hpartition Forall_app in Hall. destruct Hall as [_ Hcurrent].
  have Hvalid := Forall_inv Hcurrent.
  have Hvalue := access_entry_count_value entry Hvalid.
  have Haddress : bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744.
  { clear -Hlow Hhigh. bv_solve. }
  iEval (rewrite Haddress) in "Hcopied".
  iEval (unfold accessEntryAfterAddressEvents; rewrite -Hvalue) in "Htrace".
  unfold accessCountWholeEntry, accessCountWholeFrame.
  iFrame "Hsys Hsp Hra H5 Hdata Hsize Hstack Hmmio Htrace Hnext Hcopied".
  iSplit; first (iPureIntro; exact (proj1 Hvalid)).
  iSplit; first done. iSplit; first done.
  iSplit; first (iPureIntro; clear -Hhigh; lia).
  unfold accessCountLoopFrame, accessCountLoopScratch. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions access_count_loop_entry_resources.
