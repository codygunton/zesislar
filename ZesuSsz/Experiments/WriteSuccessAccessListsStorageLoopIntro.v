From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessLoopCommon.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsStorageFrame.

Lemma write_success_access_lists_storage_exit_pre
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp pointer : bv 64) (count : nat) (storageBytes : list (bv 8))
    (storageTail : spec) :
  instr_body 0x153b4 (writeSuccessAccessListsTailSpec x19 P) -∗
  instr_pre 0x153b4
    (writeSuccessStorageKeysLoopExit x19 sp (bv_unsigned pointer)
      (S count) storageBytes storageTail
      (writeSuccessAccessListsStorageFrame x19 P sp (bv_unsigned pointer)
        (S count) storageBytes storageTail)).
Proof.
  iIntros "Hnext".
  iEval (rewrite instr_pre'_eq) in "Hnext".
  rewrite instr_pre'_eq.
  iNext. iIntros "Hexit".
  iApply "Hnext".
  iApply (write_success_access_lists_storage_exit x19 P sp
    (bv_unsigned pointer) (S count) storageBytes storageTail with "Hexit").
Qed.

Lemma write_success_access_lists_storage_loop_intro
    `{!islaG Sigma} `{!threadG} (x19 sp pointer : bv 64)
    (count : nat) (storageBytes : list (bv 8)) (storageTail : spec)
    (Frame : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessStorageKeysOtherRegShapes ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x22" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S count))) ∗
   bv_unsigned pointer ↦ₘ∗ storageBytes ∗
   writeSuccessStorageKeysScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessStorageKeysEvents sp (S count) storageTail) ∗
   Frame ∗
   writeSuccessFixedWidthArrayInvariant sp pointer (bv_unsigned pointer)
     (S count) O count storageBytes ∗ True) -∗
  instr_pre 0x153b4
    (writeSuccessStorageKeysLoopExit x19 sp (bv_unsigned pointer)
      (S count) storageBytes storageTail Frame) -∗
  writeSuccessStorageKeysLoopSpec x19 Frame.
Proof.
  iIntros "(Hsys & Hregs & Hx19 & Hx2 & Hx22 & Hx27 & Hbytes & Hscratch &
    Hmmio & Htrace & HP & Hinv & _) Hexit".
  rewrite /writeSuccessStorageKeysLoopSpec.
  iExists sp, pointer, (bv_unsigned pointer), (S count), O, count,
    storageBytes, storageTail.
  iFrame.
Qed.
