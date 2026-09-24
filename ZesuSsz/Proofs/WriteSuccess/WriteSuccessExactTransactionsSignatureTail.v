Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_33 Require Import instrs.

Definition transactionSignatureTailEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗ reg_col [(KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 184) ↦ₘ? 8 ∗
   (bv_unsigned sp + 208) ↦ₘ? 8 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 136 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 216 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureTailEntry) := I.

Definition transactionSignatureTailPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowWord bytes index 128) ∗
   base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 208) ↦ₘ (transactionRowWord bytes index 128) ∗
   (bv_unsigned sp + 184) ↦ₘ (transactionRowWord bytes index 120) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 136 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 216 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureTailPost) := I.

Lemma transactions_signature_tail_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_33.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15098 (transactionSignatureTailPost sp row base bytes index P) -∗
  instr_body 0x15088 (transactionSignatureTailEntry sp row base bytes index P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_signature_tail_correct.
