Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma encoder_boolean_exact_output `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 4
      IslaTraces.write_success_03.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 9)%bv
    (BV 64 1) (BV 64 0x15bbc) [bv_extract 0 8 (bv_and value (BV 64 1))]
    tail ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗ P ∗ True)) -∗
  instr_body 0x15bbc
    (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15bbc) ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
     "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
     bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗
       [bv_extract 0 8 (bv_and value (BV 64 1))] ∗
     mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
     ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗ P ∗ True) ∗ True) -∗
  instr_body 0x15bac
    (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
     "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x10" ↦ᵣ RVal_Bits (bv_and value (BV 64 1)) ∗
     "x11" ↦ᵣ RVal_Bits old_x11 ∗
     bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗
       [bv_extract 0 8 (bv_and value (BV 64 1))] ∗
     mmio_range 0x2401a0c0 16 ∗
     spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
       [bv_extract 0 8 (bv_and value (BV 64 1))] tail) ∗
     ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗ P ∗ True) ∗ True).
Proof.
  zesu_block.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: lazymatch goal with |- ?G => fail "Boolean output residual" G end.
Qed.

Print Assumptions encoder_boolean_exact_output.
