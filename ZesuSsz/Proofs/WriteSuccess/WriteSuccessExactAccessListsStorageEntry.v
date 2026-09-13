Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBranchEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageWholeBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsEntryValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOwnership.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysNativeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessStorageLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries processed : list writeSuccessAccessEntry)
    (entry : writeSuccessAccessEntry) (rest : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (savedX22 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn processed ∗ writeSuccessAccessEntriesOwn rest ∗
   ⌜writeSuccessAccessEntryValid entry⌝ ∗
   ⌜writeSuccessAccessEntryStorageCount entry <> 0%nat ->
     0x20000000 <= bv_unsigned (writeSuccessAccessEntryStoragePointer entry)⌝ ∗
   ⌜writeSuccessAccessEntryStorageCount entry <> 0%nat ->
     bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
       Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) < 0x40000000⌝ ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ writeSuccessAccessEntryBytes entry ∗
   (bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   ⌜entries = processed ++ entry :: rest⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   ⌜entries <> [] -> 0x20000000 <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessStorageLoopFrame) := I.

Lemma access_storage_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  (accessListsStorageWholeBranchPost sp (sp - BV 64 16)%bv (writeSuccessAccessEntryBytes entry)
    (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P) ∗
   ⌜transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 <> BV 64 0⌝ ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp
     (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
     (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
     (writeSuccessExactAccessListsEvents sp rest tail)
     (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P)) ∗ True)%I -∗
  ∃ n : nat, storageKeysExactEntry x19 sp (writeSuccessAccessEntryStoragePointer entry) n
    (writeSuccessAccessEntryStorageBytes entry) (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P).
Proof.
  iIntros "(Hpost & %Hne & Hnext & _)". iDestruct "Hpost" as
    "(Hsys & Hsp & Hdata & Hptr & Hcounter & Hcopied & %Hrowlen & %Hrowalign & %Hrowlow &
     %Hrowhigh & Hframe & _)".
  iDestruct "Hframe" as "(Htmp & Hregs & H19 & Hra & H5 & Hsize & Hbytes & Hown & Hscratch &
    Hstack & Hmmio & Htrace & %Hpartition & Hencoding & Hlength & Htotalbound & %Halign &
    %Hlow & Hhigh & Hbaselow & Hbasehigh & HP & _)".
  iEval (rewrite Hpartition access_entries_own_app; cbn [writeSuccessAccessEntriesOwn]) in "Hown".
  iDestruct "Hown" as "(Hprocessed & (Hentry & Hrest & _) & _)".
  iDestruct "Hentry" as "(Hstorage & %Hvalid & _)".
  have Hptr := access_entry_pointer_value entry Hvalid.
  have Hword : transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 =
    Z_to_bv 64 (Z.of_nat (writeSuccessAccessEntryStorageCount entry)) by exact (proj1 (proj2 (proj2 Hvalid))).
  have Hpositive : writeSuccessAccessEntryStorageCount entry <> 0%nat.
  { intros Hz. apply Hne. rewrite Hword Hz. apply bv_eq. vm_compute. done. }
  destruct (writeSuccessAccessEntryStorageCount entry) as [|n] eqn:Hsucc; first contradiction.
  iEval (rewrite Hptr) in "Hptr". iEval (rewrite Hword) in "Hcounter".
  iEval (unfold writeSuccessAccessEntryStorageOwn; rewrite Hsucc) in "Hstorage".
  iDestruct "Hstorage" as "(Hkeys & %Hkeylow & %Hkeyhigh & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hkeyscratch & _)".
  iAssert (reg_col writeSuccessStorageKeysOtherRegShapes ∗ True)%I
    with "[Htmp Hregs Hra H5 Hdata Hsize]" as "[Hother _]".
  { unfold accessRegisterGroup, accessUnchangedRegisters,
      writeSuccessStorageKeysOtherRegShapes, writeSuccessStorageKeysOtherRegisters. zesu_run. }
  iEval (unfold accessEntryAfterCountEvents; rewrite Hsucc) in "Htrace".
  iExists n. unfold storageKeysExactEntry.
  iFrame "Hsys Hother H19 Hsp Hptr Hcounter Hkeys Hkeyscratch Hmmio Htrace Hnext".
  iSplit; first (iPureIntro; rewrite -Hsucc; exact (proj1 (proj2 (proj2 (proj2 Hvalid))))).
  iSplit; first (iPureIntro; rewrite -Hsucc; exact (proj2 (proj2 (proj2 (proj2 Hvalid))))).
  iSplit; first done. iSplit; first (iPureIntro; clear -Hlow; lia).
  iSplit; first done. iSplit; first done. iSplit; first done.
  unfold accessStorageLoopFrame. iFrame.
  repeat iSplit; try done; iPureIntro; unfold writeSuccessAccessEntryValid in Hvalid; tauto.
Qed.
Print Assumptions access_storage_loop_entry_resources.
