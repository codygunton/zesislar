Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysWords
  WriteSuccessExactStorageKeysFixedBytes.

Definition storageKeysWidePost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyEight bytes index 0) ∗
   "x12" ↦ᵣ RVal_Bits (storageKeyEight bytes index 8) ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyEight bytes index 16) ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyEight bytes index 24) ∗
   reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x24"; "x25"; "x26"; "x1"; "x18"; "x23"; "x31"; "x30"; "x29";
      "x16"; "x8"; "x21"; "x20"; "x9"; "x7"; "x28";
      "x17"; "x5"; "x6"; "x15"; "x11"]) ∗
   storageKeysWordFrame row base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysWidePost) := I.

Lemma storage_keys_wide_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 (drop 8 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15388 (storageKeysWidePost row base bytes index P) -∗
  instr_body 0x15368 (storageKeysWordsPost row base bytes index P).
Proof.
  zesu_block.
  all: unfold storageKeyEight, storageKeyFour; cbn [seq fmap Nat.add]; apply array_byte_eight.
Qed.
Print Assumptions storage_keys_wide_correct.
