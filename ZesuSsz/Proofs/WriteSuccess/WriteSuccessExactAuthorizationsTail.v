Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_82 Require Import instrs.

Definition authorizationTailState `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   "x18" ↦ᵣ RVal_Bits count ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationTailState) := I.

Lemma authorization_tail_pre_correct `{!islaG Sigma} `{!threadG}
    pointer count (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_82.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x15590 (authorizationTailState (pointer + BV 64 144)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv <> BV 64 0⌝ ∗ True) -∗
  instr_pre 0x15620 (authorizationTailState (pointer + BV 64 144)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv = BV 64 0⌝ ∗ True) -∗
  instr_body 0x15614 (authorizationTailState pointer count P).
Proof.
  zesu_block.
  all: replace (count - BV 64 1)%bv
    with (count + BV 64 18446744073709551615)%bv by bv_solve; assumption.
Qed.
Print Assumptions authorization_tail_pre_correct.
