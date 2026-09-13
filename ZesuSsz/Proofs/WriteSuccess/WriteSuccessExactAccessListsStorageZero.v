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

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.

Lemma access_storage_zero_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  (accessListsStorageWholeBranchPost sp (sp - BV 64 16)%bv (writeSuccessAccessEntryBytes entry)
    (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P) ∗
   ⌜transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 = BV 64 0⌝ ∗ True)%I -∗
  writeSuccessStorageKeysLoopExit x19 sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P).
Proof.
  iIntros "(Hpost & %Heq & _)". iDestruct "Hpost" as
    "(Hsys & Hsp & Hdata & Hptr & Hcounter & Hcopied & %Hrowlen & %Hrowalign & %Hrowlow &
     %Hrowhigh & Hframe & _)".
  iDestruct "Hframe" as "(Htmp & Hregs & H19 & Hra & H5 & Hsize & Hbytes & Hown & Hscratch &
    Hstack & Hmmio & Htrace & %Hpartition & Hencoding & Hlength & Htotalbound & %Halign &
    %Hlow & Hhigh & Hbaselow & Hbasehigh & HP & _)".
  iEval (rewrite Hpartition access_entries_own_app; cbn [writeSuccessAccessEntriesOwn]) in "Hown".
  iDestruct "Hown" as "(Hprocessed & (Hentry & Hrest & _) & _)".
  iDestruct "Hentry" as "(Hstorage & %Hvalid & _)".
  have Hptr := access_entry_pointer_value entry Hvalid.
  have Hvalue := access_entry_count_value entry Hvalid.
  have Hzero : writeSuccessAccessEntryStorageCount entry = 0%nat.
  { apply Nat2Z.inj. apply (f_equal bv_unsigned) in Heq. rewrite Hvalue in Heq. exact Heq. }
  have Hkeysnil : writeSuccessAccessEntryStorageBytes entry = [].
  { apply length_zero_iff_nil. have Hlen := proj1 (proj2 (proj2 (proj2 Hvalid))).
    rewrite Hzero in Hlen. exact Hlen. }
  iEval (rewrite Hptr) in "Hptr". iEval (rewrite Heq) in "Hcounter".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hkeyscratch & _)".
  iAssert (reg_col writeSuccessStorageKeysOtherRegShapes ∗ True)%I
    with "[Htmp Hregs Hra H5 Hdata Hsize]" as "[Hother _]".
  { unfold accessRegisterGroup, accessUnchangedRegisters,
      writeSuccessStorageKeysOtherRegShapes, writeSuccessStorageKeysOtherRegisters. zesu_run. }
  iEval (unfold accessEntryAfterCountEvents; rewrite Hzero; cbn [writeSuccessExactStorageKeysEvents]) in "Htrace".
  unfold writeSuccessStorageKeysLoopExit. iExists (writeSuccessAccessEntryStoragePointer entry).
  iFrame "Hsys Hother H19 Hsp Hptr Hcounter Hkeyscratch Hmmio Htrace".
  iSplitR.
  { rewrite Hkeysnil mem_mapsto_array_eq /mem_mapsto_array_def /=.
    iExists 1%N. iSplit; first done. iSplit; last done.
    iPureIntro. clear -entry.
    have Hrange := bv_unsigned_in_range 64 (writeSuccessAccessEntryStoragePointer entry).
    unfold bv_modulus in Hrange. lia. }
  iSplitL.
  { unfold accessStorageLoopFrame. iFrame.
    repeat iSplit; try done; iPureIntro; unfold writeSuccessAccessEntryValid in Hvalid; tauto. }
  iSplit; last done. iPureIntro. rewrite Hzero. ring.
Qed.
Print Assumptions access_storage_zero_resources.
