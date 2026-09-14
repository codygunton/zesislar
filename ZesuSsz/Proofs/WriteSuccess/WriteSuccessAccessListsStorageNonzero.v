Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorageFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorageRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorageFrameIntro.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorageInvariant.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorageLoopIntro.

Lemma write_success_access_lists_nonzero_storage_to_loop
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) (savedX22 x10 x11 : bv 64)
    (tail : spec)
    (Hnonzero : writeSuccessAccessEntryWord entry 8 <> BV 64 0) :
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessAccessListsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessAccessEntryWord entry 0) ∗
   "x27" ↦ᵣ RVal_Bits (writeSuccessAccessEntryWord entry 8) ∗
   base ↦ₘ∗ prefix ∗
   (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessAccessEntriesOwn processed ∗
   writeSuccessAccessEntryStorageOwn entry ∗
   ⌜writeSuccessAccessEntryValid entry⌝ ∗
   writeSuccessAccessEntriesOwn remaining ∗
   writeSuccessAccessListsCopiedScratch
     sp base (length entries) (length processed) entry savedX22 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessStorageKeysEvents sp
       (writeSuccessAccessEntryStorageCount entry)
       (writeSuccessAccessListsEvents sp remaining tail)) ∗ P ∗
   writeSuccessAccessListsInvariant sp base entries processed
     (entry :: remaining) bytes prefix suffix ∗
   instr_pre 0x153c0
     (writeSuccessAccessListsLoopExit
       sp base entries bytes tail x19 savedX22 P) ∗
   instr_body 0x153b4 (writeSuccessAccessListsTailSpec x19 P) ∗ True) -∗
  writeSuccessAccessListsStorageAnyLoopSpec x19 P.
Proof.
  iIntros "(Hsys & Hregs & Hx2 & Hx10 & Hx19 & Hx11 & Hx22 & Hx27 &
    Hprefix & Hsuffix & Hprocessed & HentryStorage & %Hvalid & Hremaining &
    Hcopied & Hmmio & Htrace & HP & #Hinv & Hexit & Hnext & _)".
  destruct Hvalid as
    [HentryLength [Hpointer [Hcount [HstorageLength HcountBound]]]].
  have Hvalid : writeSuccessAccessEntryValid entry :=
    conj HentryLength
      (conj Hpointer (conj Hcount (conj HstorageLength HcountBound))).
  destruct (writeSuccessAccessEntryStorageCount entry) as [|count]
    eqn:HcountCase.
  { exfalso. apply Hnonzero. rewrite Hcount.
    apply bv_eq. rewrite bv_unsigned_BV Z_to_bv_unsigned. reflexivity. }
  iEval (rewrite /writeSuccessAccessEntryStorageOwn HcountCase)
    in "HentryStorage".
  iDestruct "HentryStorage" as
    "(HstorageBytes & %HstorageLow & %HstorageHigh & _)".
  iPoseProof (write_success_access_lists_storage_invariant sp base entry
    entries processed remaining bytes prefix suffix count HstorageLength
    HcountBound HstorageLow HstorageHigh with "Hinv") as "HstorageInv".
  iAssert (reg_col writeSuccessStorageKeysOtherRegShapes)%I
    with "[Hregs Hx10 Hx11]" as "HstorageRegs".
  { iApply (write_success_access_lists_storage_registers x10 x11 with
      "Hregs Hx10 Hx11"). }
  iPoseProof (write_success_access_lists_storage_frame_intro
    x19 P sp base entry entries processed remaining bytes prefix suffix
    savedX22 x10 x11 tail count HcountCase Hvalid HstorageLow HstorageHigh with
    "[Hprefix Hsuffix Hprocessed Hremaining Hcopied HP Hexit]") as
    "(HstorageScratch & Hframe)".
  { iFrame. done. }
  iEval (rewrite Hpointer) in "Hx22".
  iEval (rewrite Hcount) in "Hx27".
  iPoseProof (write_success_access_lists_storage_exit_pre x19 P sp
    (writeSuccessAccessEntryStoragePointer entry) count
    (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessAccessListsEvents sp remaining tail) with "Hnext") as
    "HstorageExit".
  iAssert
    (reg_col zesu_ram_sys_regs ∗
     reg_col writeSuccessStorageKeysOtherRegShapes ∗
     "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x22" ↦ᵣ RVal_Bits (writeSuccessAccessEntryStoragePointer entry) ∗
     "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S count))) ∗
     bv_unsigned (writeSuccessAccessEntryStoragePointer entry) ↦ₘ∗
       writeSuccessAccessEntryStorageBytes entry ∗
     writeSuccessStorageKeysScratch sp ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace
       (writeSuccessStorageKeysEvents sp (S count)
         (writeSuccessAccessListsEvents sp remaining tail)) ∗
     writeSuccessAccessListsStorageFrame x19 P sp
       (bv_unsigned (writeSuccessAccessEntryStoragePointer entry)) (S count)
       (writeSuccessAccessEntryStorageBytes entry)
       (writeSuccessAccessListsEvents sp remaining tail) ∗
     WriteSuccessLoopCommon.writeSuccessFixedWidthArrayInvariant sp
       (writeSuccessAccessEntryStoragePointer entry)
       (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
       (S count) O count (writeSuccessAccessEntryStorageBytes entry) ∗ True)%I
    with "[Hsys HstorageRegs Hx19 Hx2 Hx22 Hx27 HstorageBytes
      HstorageScratch Hmmio Htrace Hframe]" as "HloopResources".
  { iFrame "Hsys HstorageRegs Hx19 Hx2 Hx22 Hx27 HstorageBytes
      HstorageScratch Hmmio Htrace Hframe HstorageInv". }
  iPoseProof (write_success_access_lists_storage_loop_intro x19 sp
    (writeSuccessAccessEntryStoragePointer entry) count
    (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessAccessListsEvents sp remaining tail)
    (writeSuccessAccessListsStorageFrame x19 P sp
      (bv_unsigned (writeSuccessAccessEntryStoragePointer entry)) (S count)
      (writeSuccessAccessEntryStorageBytes entry)
      (writeSuccessAccessListsEvents sp remaining tail)) with
    "HloopResources HstorageExit") as "HloopSpec".
  rewrite /writeSuccessAccessListsStorageAnyLoopSpec.
  iExists sp, (bv_unsigned (writeSuccessAccessEntryStoragePointer entry)),
    (S count), (writeSuccessAccessEntryStorageBytes entry),
    (writeSuccessAccessListsEvents sp remaining tail).
  iExact "HloopSpec".
Qed.
