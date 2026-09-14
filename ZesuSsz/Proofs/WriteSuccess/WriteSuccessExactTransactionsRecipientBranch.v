Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_44 Require Import instrs.

Definition transactionRecipientBranchState `{!islaG Sigma} `{!threadG}
    (sp tag data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits data ∗ (bv_unsigned sp + 120) ↦ₘ tag ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 128 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientBranchState) := I.

Lemma transactions_recipient_branch_correct `{!islaG Sigma} `{!threadG}
    sp tag old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_44.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1515c (transactionRecipientBranchState sp tag tag P ∗
    ⌜tag <> BV 64 0⌝ ∗ True) -∗
  instr_body 0x15194 (transactionRecipientBranchState sp tag tag P ∗
    ⌜tag = BV 64 0⌝ ∗ True) -∗
  instr_body 0x15154 (transactionRecipientBranchState sp tag old_data P).
Proof. zesu_block. Qed.
Print Assumptions transactions_recipient_branch_correct.
