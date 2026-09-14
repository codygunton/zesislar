Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionRowWord (bytes : list (bv 8)) (index offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + offset)%nat bytes))).

Definition transactionGasLoadEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x25", BitsShape 64); (KindReg "x24", BitsShape 64);
     (KindReg "x9", BitsShape 64); (KindReg "x23", BitsShape 64)] ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLoadEntry) := I.

Definition transactionGasLoadPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowWord bytes index 0) ∗
   "x24" ↦ᵣ RVal_Bits (transactionRowWord bytes index 8) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowWord bytes index 16) ∗
   "x23" ↦ᵣ RVal_Bits (transactionRowWord bytes index 24) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLoadPost) := I.

Lemma transactions_gas_loads_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f2c (transactionGasLoadPost row base bytes index P) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowWord; rewrite ?Nat.add_0_r; reflexivity.
Qed.
Print Assumptions transactions_gas_loads_correct.

