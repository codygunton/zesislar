Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) : isla_coq_rewrite.

Lemma encoder_boolean_exact_suffix `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 8 IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bbc
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x15bbc) ∗
     "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
     (bv_unsigned sp - 8) ↦ₘ ret ∗
     ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
     ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
     ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
     ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
     ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
     ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
     instr_pre (bv_unsigned ret)
       (reg_col zesu_ram_sys_regs ∗
        "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
        (bv_unsigned sp - 8) ↦ₘ ret ∗ P ∗ True) ∗ True).
Proof. move => *. zesu_block. Qed.

Print Assumptions encoder_boolean_exact_suffix.
