Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageWholeBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessBranchLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail trace : spec) (P : iProp Sigma) : iProp Sigma :=
  (accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗ accessRegisterGroup accessUnchangedRegisters ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1521c) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗ "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   accessCountLoopScratch sp base (length entries) (length processed) savedX22 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace trace ∗
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
Global Instance : LithiumUnfold (@accessBranchLoopFrame) := I.


Lemma access_branch_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  accessCountWholePost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P) -∗
  accessListsStorageWholeBranchEntry sp (sp - BV 64 16)%bv (writeSuccessAccessEntryBytes entry)
    (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as
    "(Hsys & Hra & Hsp & H5 & Hdata & Hsize & Hstack & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hcopied & %Hrowlen & %Hrowalign & %Hrowlow & %Hrowhigh & Hframe & _)".
  iDestruct "Hframe" as "(Htmp & Hrest & H19 & H22 & H27 & Hbytes & Hown & Hscratch &
    Hpartition & Hencoding & Hlength & Hcount & Halign & Hlow & Hhigh &
    Hbaselow & Hbasehigh & HP & _)".
  iAssert (reg_col [(KindReg "x22", BitsShape 64); (KindReg "x27", BitsShape 64)] ∗ True)%I
    with "[H22 H27]" as "[Hregs _]".
  { zesu_run. }
  unfold accessListsStorageWholeBranchEntry.
  iFrame "Hsys Hsp Hdata Hregs Hcopied".
  iSplit; first done.
  iSplit; first (iPureIntro; exact (stack_align8_from16 sp Hrowalign)).
  iSplit; first (iPureIntro; clear -Hrowlow; lia).
  iSplit; first done.
  unfold accessBranchLoopFrame. iFrame.
Qed.
Print Assumptions access_branch_loop_entry_resources.
