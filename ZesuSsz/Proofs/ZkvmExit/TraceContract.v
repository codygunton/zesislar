Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuSsz.Export.Snapshots.

Import ZesuSsz.Automation.Hooks.

Require Import ZesuSsz.Proofs.ZkvmExit.ZkvmExit.
Definition zkvmExitTailResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
    IslarisContractResources ZkvmExitArgs unit := {|
  islarisCode :=
    (instr 0x101c4 (Some a101c4) ∗
     instr 0x101c8 (Some a101c8) ∗
     instr 0x101cc (Some a101cc))%I;
  islarisEntry := fun args =>
    (∃ (code old_x5 old_exit_code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      mmio_range (machineExitAddress defaultMap) 8 ∗
      spec_trace (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) code) tail) ∗ P ∗ True)%I;
  islarisExit := fun args _ =>
    (∃ (code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      mmio_range (machineExitAddress defaultMap) 8 ∗ spec_trace tail ∗ P ∗ True)%I
|}.



Theorem zkvm_exit_tail_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x101c4 0x101d0
    zkvmExitAllows (zkvmExitTailResources tail P).
Proof.
  rewrite /IslarisContractSpec /zkvmExitTailResources /=.
  zesu_block.
  liInst (λ x, x.1ₗ = code).
  zesu_run.
Qed.


Print Assumptions zkvm_exit_tail_state_correct.
