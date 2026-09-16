Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import isla.riscv64.riscv64.

Definition storageKeysExactEntry `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) (remaining : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessStorageKeysOtherRegShapes ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x22" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactStorageKeysEvents sp 0 (S remaining) bytes tail) ∗
   ⌜length bytes = (32 * S remaining)%nat⌝ ∗
   ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp (bv_unsigned pointer)
     (S remaining) bytes tail P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysExactEntry) := I.

Lemma storage_keys_exact_entry_resources `{!islaG Sigma} `{!threadG}
    x19 sp pointer remaining bytes tail (P : iProp Sigma) :
  storageKeysExactEntry x19 sp pointer remaining bytes tail P -∗
  writeSuccessExactStorageKeysLoopSpec x19 P.
Proof.
  iIntros "(Hsys & Hregs & H19 & Hsp & Hptr & Hcount & Hbytes & Hscratch &
    Hmmio & Htrace & %Hlen & %Hcount & %Halign & %Hlow & %Hhigh &
    %Hbase & %Hend & Hnext & HP & _)".
  iExists sp, pointer, (bv_unsigned pointer), (S remaining), 0%nat, remaining, bytes, tail.
  iFrame. unfold writeSuccessFixedWidthArrayInvariant.
  repeat iSplit; try done.
  iPureIntro. ring.
Qed.
Print Assumptions storage_keys_exact_entry_resources.
