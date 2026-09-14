Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysWords WriteSuccessExactStorageKeysFixedBytes.
From IslaTraces.write_success_69 Require Import instrs.

Definition blobWordFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits row ∗ "x27" ↦ᵣ RVal_Bits count ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@blobWordFrame) := I.

Definition blobFourWordsPost `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyFour bytes index 16) ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyFour bytes index 20) ∗
   "x8" ↦ᵣ RVal_Bits (storageKeyFour bytes index 8) ∗
   "x17" ↦ᵣ RVal_Bits (storageKeyFour bytes index 12) ∗
   "x5" ↦ᵣ RVal_Bits (storageKeyFour bytes index 0) ∗
   "x15" ↦ᵣ RVal_Bits (storageKeyFour bytes index 4) ∗
   "x11" ↦ᵣ RVal_Bits (storageKeyFour bytes index 24) ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyFour bytes index 28) ∗
   reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x6"; "x7"; "x9"; "x12"; "x16"; "x18"; "x20"; "x21"; "x22";
      "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"]) ∗
   blobWordFrame row count base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobFourWordsPost) := I.

Definition blobWidePost `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyEight bytes index 0) ∗
   "x12" ↦ᵣ RVal_Bits (storageKeyEight bytes index 8) ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyEight bytes index 16) ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyEight bytes index 24) ∗
   reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x5"; "x6"; "x7"; "x8"; "x9"; "x11"; "x15"; "x16"; "x17"; "x18";
      "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"]) ∗
   blobWordFrame row count base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobWidePost) := I.

Lemma blob_wide_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 (drop 9 IslaTraces.write_success_69.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15538 (blobWidePost row count base bytes index P) -∗
  instr_body 0x15518 (blobFourWordsPost row count base bytes index P).
Proof.
  zesu_block.
  all: unfold storageKeyEight, storageKeyFour; cbn [seq fmap Nat.add]; apply array_byte_eight.
Qed.
Print Assumptions blob_wide_correct.
