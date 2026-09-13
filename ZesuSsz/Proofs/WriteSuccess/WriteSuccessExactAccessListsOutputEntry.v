Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyRange.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsValidity.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessEntryAfterAddressEvents (sp : bv 64) (entry : writeSuccessAccessEntry)
    (rest : list writeSuccessAccessEntry) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (Z.of_nat (writeSuccessAccessEntryStorageCount entry))))
    (writeSuccessExactStorageKeysEvents sp 0 (writeSuccessAccessEntryStorageCount entry)
      (writeSuccessAccessEntryStorageBytes entry) (writeSuccessExactAccessListsEvents sp rest tail)).

Definition accessOutputLoopScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total processed : nat) (savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 272) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ writeSuccessStorageKeysScratch sp ∗ True)%I.
Global Instance : LithiumUnfold (@accessOutputLoopScratch) := I.

Definition accessOutputLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗ accessRegisterGroup accessUnchangedRegisters ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   accessOutputLoopScratch sp base (length entries) (length processed) savedX22 ∗
   ⌜entries = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   ⌜entries <> [] -> 0x20000000 <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@accessOutputLoopFrame) := I.



Lemma access_output_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  accessCopyWholePost sp (Z_to_bv 64 base) (Z_to_bv 64 (Z.of_nat (length processed))) bytes
    (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P) -∗
  ∃ old5 : bv 64, accessListsWholeOutputEntry sp (BV 64 0x15200) old5
    (sp + BV 64 1744)%bv (Z_to_bv 64 (base + 40 * Z.of_nat (length processed)))
    (writeSuccessAccessEntryBytes entry) (accessEntryAfterAddressEvents sp entry rest tail)
    (accessOutputLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as (final13 final14)
    "(Hsys & Hra & Hdata & Hsrc & Hsize & H13 & H14 & H15 & Hbytes & Hcopied & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & Hbase & Hindex & Hframe & _)".
  iDestruct "Hframe" as "(H5 & Hrest & H19 & H22 & H27 & Hown & Hscratch &
    Hmmio & Htrace & %Hpartition & %Hencoding & %Hlength & Hcount & %Halign & %Hlow & %Hhigh &
    %Hbaselow & %Hbasehigh & HP & _)".
  have Hnonempty : entries <> [] by (rewrite Hpartition; destruct processed; discriminate).
  have Hvalues := access_copy_processed_values base entries processed (entry :: rest) bytes
    Hpartition Hlength (Hbaselow Hnonempty) (Hbasehigh Hnonempty).
  destruct Hvalues as [Hcur Hroot].
  iEval (rewrite Hroot) in "Hbytes". iEval (rewrite Hroot Hcur) in "Hsrc".
  iDestruct (access_entries_validity with "Hown") as "[%Hall Hown]".
  rewrite Hpartition Forall_app in Hall. destruct Hall as [Hprocessed Hcurrent].
  have Hvalid := Forall_inv Hcurrent.
  have Hcopy := access_entries_bytes_slice processed entry rest Hprocessed Hvalid.
  rewrite -Hpartition -Hencoding in Hcopy.
  iEval (rewrite Hcur Nat2Z.id Hcopy) in "Hcopied".
  iEval (cbn [writeSuccessExactAccessListsEvents]; rewrite access_entry_exact_events) in "Htrace".
  iEval (unfold accessRegisterGroup; rewrite reg_col_cons reg_col_nil) in "H5".
  iDestruct "H5" as "((%v5 & %Hv5 & H5) & _)".
  destruct (valu_has_bits_shape _ _ Hv5) as [old5 ->].
  iAssert (accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗ True)%I
    with "[Hsize H13 H14 H15]" as "[Htmp _]".
  { unfold accessRegisterGroup. zesu_run. }
  iDestruct "Hscratch" as "(Hsaved & Htotal & Hstack & Hkeys & _)".
  iExists old5. unfold accessListsWholeOutputEntry.
  iFrame "Hsys Hsp Hra H5 Hdata Hsrc Hcopied Hmmio Htrace".
  iSplit; first (iPureIntro; exact (proj1 Hvalid)).
  iSplit; first (iPureIntro; clear -Hlow; lia).
  iSplit; first (iPureIntro; clear -Hhigh; lia).
  unfold accessOutputLoopFrame, accessOutputLoopScratch. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions access_output_loop_entry_resources.
