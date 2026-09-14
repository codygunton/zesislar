Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayWordValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysShiftsHandoff
  WriteSuccessExactStorageKeysRemainingShifts.
From IslaTraces.write_success_60 Require Import instrs.
From IslaTraces.write_success_61 Require Import instrs.

Definition storageKeyFour (bytes : list (bv 8)) (index offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8
    [storageKeyByte bytes index offset; storageKeyByte bytes index (offset + 1);
     storageKeyByte bytes index (offset + 2); storageKeyByte bytes index (offset + 3)]).

Definition storageKeysWordFrame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysWordFrame) := I.

Definition storageKeysWordsPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyFour bytes index 16) ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyFour bytes index 20) ∗
   "x17" ↦ᵣ RVal_Bits (storageKeyFour bytes index 8) ∗
   "x5" ↦ᵣ RVal_Bits (storageKeyFour bytes index 12) ∗
   "x6" ↦ᵣ RVal_Bits (storageKeyFour bytes index 0) ∗
   "x15" ↦ᵣ RVal_Bits (storageKeyFour bytes index 4) ∗
   "x11" ↦ᵣ RVal_Bits (storageKeyFour bytes index 24) ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyFour bytes index 28) ∗
   reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x24"; "x25"; "x26"; "x1"; "x18"; "x23"; "x31"; "x30"; "x29";
      "x16"; "x12"; "x8"; "x21"; "x20"; "x9"; "x7"; "x28"]) ∗
   storageKeysWordFrame row base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysWordsPost) := I.

Lemma storage_keys_words_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 15 IslaTraces.write_success_60.instrs.instr_map ++
    take 8 IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15368 (storageKeysWordsPost row base bytes index P) -∗
  instr_body 0x15324 (storageKeysRemainingShiftsPost
    (storageKeyByte bytes index 14)
    (storageKeyByte bytes index 15)
    (storageKeyByte bytes index 1)
    (storageKeyByte bytes index 2)
    (storageKeyByte bytes index 3)
    (storageKeyByte bytes index 5)
    (storageKeyByte bytes index 6)
    (storageKeyByte bytes index 7)
    (storageKeyByte bytes index 25)
    (storageKeyByte bytes index 26)
    (storageKeyByte bytes index 27)
    (storageKeyByte bytes index 29)
    (storageKeyByte bytes index 30)
    (storageKeyByte bytes index 31)
    (storageKeysShiftsFrame row base bytes index P)).
Proof.
  zesu_block.
  all: rewrite ?(storage_keys_row_byte bytes index 0 ltac:(lia)).
  all: rewrite ?(storage_keys_row_byte bytes index 4 ltac:(lia)).
  all: rewrite ?(storage_keys_row_byte bytes index 24 ltac:(lia)).
  all: rewrite ?(storage_keys_row_byte bytes index 28 ltac:(lia)).
  all: unfold storageKeyFour; cbn [Nat.add]; zesu_array_word_value.
Qed.
Print Assumptions storage_keys_words_correct.
