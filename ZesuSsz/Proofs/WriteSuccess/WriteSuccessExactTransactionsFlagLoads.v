Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionRowByte (bytes : list (bv 8)) (index offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop (index + offset)%nat bytes))).

Definition transactionFlagLoadEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64)] ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 283 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFlagLoadEntry) := I.

Definition transactionFlagLoadPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   "x14" ↦ᵣ RVal_Bits (transactionRowByte bytes index 281) ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 282) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 283 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFlagLoadPost) := I.

Lemma transactions_flag_loads_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f68 (transactionFlagLoadPost row base bytes index P) -∗
  instr_body 0x14f5c (transactionFlagLoadEntry row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_flag_loads_correct.
