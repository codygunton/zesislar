Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List.
From IslaTraces.write_success_52 Require Import instrs.
From IslaTraces.write_success_53 Require Import instrs.

Definition accessListsControlState `{!islaG Sigma} `{!threadG}
    (sp count cursor data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits cursor ∗
   (bv_unsigned sp + 264) ↦ₘ count ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 272 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsControlState) := I.

Lemma access_lists_control_correct `{!islaG Sigma} `{!threadG}
    (initial : bool) sp count cursor old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ (if initial then
    IslaTraces.write_success_52.instrs.instr_map ++
      IslaTraces.write_success_53.instrs.instr_map
    else IslaTraces.write_success_53.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151dc (accessListsControlState sp count
    (if initial then BV 64 0 else cursor) count P ∗
    ⌜(if initial then BV 64 0 else cursor) <> count⌝ ∗ True) -∗
  instr_body 0x153c0 (accessListsControlState sp count
    (if initial then BV 64 0 else cursor) count P ∗
    ⌜(if initial then BV 64 0 else cursor) = count⌝ ∗ True) -∗
  instr_body (if initial then 0x151d0 else 0x151d4)
    (accessListsControlState sp count cursor old_data P).
Proof. destruct initial; zesu_block. Qed.
Print Assumptions access_lists_control_correct.
