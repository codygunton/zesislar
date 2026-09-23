Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionsThreeByteLoadEntry `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x13"; "x14"; "x15"]) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + 288 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsThreeByteLoadEntry) := I.

Definition transactionsThreeByteLoadPost `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   "x13" ↦ᵣ RVal_Bits (bv_zero_extend 64 (default (BV 8 0) (bytes !! 280%nat))) ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 (default (BV 8 0) (bytes !! 281%nat))) ∗
   "x15" ↦ᵣ RVal_Bits (bv_zero_extend 64 (default (BV 8 0) (bytes !! 282%nat))) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + 288 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsThreeByteLoadPost) := I.

Lemma transactions_three_byte_loads_correct `{!islaG Sigma} `{!threadG}
    pointer bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 3 (drop 21 IslaTraces.write_success_29.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x14f68 (transactionsThreeByteLoadPost pointer bytes P) -∗
  instr_body 0x14f5c (transactionsThreeByteLoadEntry pointer bytes P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_three_byte_loads_correct.
