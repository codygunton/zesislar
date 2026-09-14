Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma encoder_boolean_exact_prefix `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bac
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
     "x10" ↦ᵣ RVal_Bits (bv_and value (BV 64 1)) ∗
     (bv_unsigned sp - 16) ↦ₘ? 7 ∗
     (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 (bv_and value (BV 64 1))) ∗
     (bv_unsigned sp - 8) ↦ₘ ret ∗ P ∗ True) -∗
  instr_body 0x15b9c
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x10" ↦ᵣ RVal_Bits value ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
     ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
     ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
     ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗ True).
Proof.
  zesu_block.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "Boolean prefix residual" G end.
Qed.

Print Assumptions encoder_boolean_exact_prefix.
