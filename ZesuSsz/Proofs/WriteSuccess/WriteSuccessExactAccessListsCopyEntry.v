Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyRange.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCallRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessCopyLoopScratch `{!islaG Sigma}
    (sp : bv 64) (total : nat) (savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ writeSuccessStorageKeysScratch sp ∗ True)%I.
Global Instance : LithiumUnfold (@accessCopyLoopScratch) := I.

Definition accessCopyLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (accessRegisterGroup ["x5"] ∗ accessRegisterGroup accessUnchangedRegisters ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   writeSuccessAccessEntriesOwn entries ∗
   accessCopyLoopScratch sp (length entries) savedX22 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactAccessListsEvents sp remaining tail) ∗
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
Global Instance : LithiumUnfold (@accessCopyLoopFrame) := I.


Lemma access_copy_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  (writeSuccessExactAccessListsState sp base entries processed (entry :: rest) bytes
    storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
   instr_pre 0x15200 (accessCopyWholePost sp (Z_to_bv 64 base)
     (Z_to_bv 64 (Z.of_nat (length processed))) bytes
     (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex
       x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)) ∗ True) -∗
  ∃ old_ra : bv 64,
    accessCopyWholeEntry sp (Z_to_bv 64 base) (Z_to_bv 64 (Z.of_nat (length processed)))
      storedIndex old_ra bytes
      (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex
        x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P).
Proof.
  iIntros "(Hstate & Hnext & _)".
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H19 & Hdata & Hcursor & H22 & H27 &
    Hbytes & Hown & Hscratch & Hmmio & Htrace & Hpartition & Hencoding & Hlength & Hcount &
    %Halign & %Hlow & %Hhigh & %Hbaselow & %Hbasehigh & HP & _)".
  iDestruct "Hpartition" as %Hpartition. iDestruct "Hlength" as %Hlength.
  have Hnonempty : entries <> [].
  { rewrite Hpartition. destruct processed; discriminate. }
  have Hrootlow := Hbaselow Hnonempty. have Hroothigh := Hbasehigh Hnonempty.
  have Hvalues := access_copy_processed_values base entries processed (entry :: rest)
    bytes Hpartition Hlength Hrootlow Hroothigh.
  destruct Hvalues as [Hcur Hroot].
  have Hrow := access_copy_row_bound entries processed rest entry bytes Hpartition Hlength.
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hcopy & Hstack & Hkeys & _)".
  iDestruct (access_copy_call_registers with "Hregs Hdata") as
    (old_ra) "(Hra & Hcall & H5 & Hrest & _)".
  iEval (unfold accessRegisterGroup) in "Hcall".
  iExists old_ra. unfold accessCopyWholeEntry. rewrite Hroot.
  iFrame "Hsys Hsp Hcursor Hra Hcall Hbase Hindex Hbytes Hcopy Hnext".
  iSplit; first (iPureIntro; apply stack_align8_from16; assumption).
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro; lia).
  iSplit; first done. iSplit; first done.
  iSplit; first (iPureIntro; rewrite Hcur Nat2Z.id; exact Hrow).
  unfold accessCopyLoopFrame, accessCopyLoopScratch. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions access_copy_loop_entry_resources.
