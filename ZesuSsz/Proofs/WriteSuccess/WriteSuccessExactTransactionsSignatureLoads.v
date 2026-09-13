Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionSignatureLoadEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col [(KindReg "x11", BitsShape 64)] ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 224) ↦ₘ? 24 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 160 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 248 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureLoadEntry) := I.

Definition transactionSignatureLoadPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowWord bytes index 152) ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 224) ↦ₘ (transactionRowWord bytes index 152) ∗
   (bv_unsigned sp + 232) ↦ₘ (transactionRowWord bytes index 144) ∗
   (bv_unsigned sp + 240) ↦ₘ (transactionRowWord bytes index 136) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 160 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 248 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureLoadPost) := I.

Lemma transactions_signature_loads_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f44 (transactionSignatureLoadPost sp row base bytes index P) -∗
  instr_body 0x14f2c (transactionSignatureLoadEntry sp row base bytes index P).
Proof. zesu_block. Qed.
Print Assumptions transactions_signature_loads_correct.
