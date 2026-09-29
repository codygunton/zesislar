Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma exact_tail_optional_bytes_branch_handoff
    `{!islaG Sigma} `{!threadG} (sp data : bv 64) (P : iProp Sigma) :
  bv_unsigned sp `mod` 16 = 0 ->
  mapRamBase defaultMap <= bv_unsigned sp ->
  bv_unsigned sp + 80 < machineRamEnd defaultMap ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x15974 (⌜data <> BV 64 0⌝ ∗ reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x8" ↦ᵣ RVal_Bits data ∗ (bv_unsigned sp + 72) ↦ₘ data ∗ P ∗ True) -∗
  instr_pre 0x15994 (⌜data = BV 64 0⌝ ∗ reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x8" ↦ᵣ RVal_Bits data ∗ (bv_unsigned sp + 72) ↦ₘ data ∗ P ∗ True) -∗
  instr_body 0x1596c
    (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     (bv_unsigned sp + 72) ↦ₘ data ∗ P ∗ True).
Proof.
  zesu_block.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions exact_tail_optional_bytes_branch_handoff.
