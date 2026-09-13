Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_62 Require Import instrs.

Definition storageKeysTailState `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits count ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysTailState) := I.

Lemma storage_keys_tail_correct `{!islaG Sigma} `{!threadG}
    pointer count (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15228 (storageKeysTailState (pointer + BV 64 32)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv <> BV 64 0⌝ ∗ True) -∗
  instr_body 0x153b4 (storageKeysTailState (pointer + BV 64 32)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv = BV 64 0⌝ ∗ True) -∗
  instr_body 0x153a8 (storageKeysTailState pointer count P).
Proof.
  zesu_block.
  all: replace (count - BV 64 1)%bv
    with (count + BV 64 18446744073709551615)%bv by bv_solve; assumption.
Qed.
Print Assumptions storage_keys_tail_correct.
