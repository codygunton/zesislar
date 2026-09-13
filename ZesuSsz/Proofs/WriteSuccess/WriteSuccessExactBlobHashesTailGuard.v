Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_71 Require Import instrs.

Definition blobTailState `{!islaG Sigma} `{!threadG}
    (pointer count value22 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits count ∗ "x22" ↦ᵣ RVal_Bits value22 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobTailState) := I.

Lemma blob_tail_pre_correct `{!islaG Sigma} `{!threadG}
    pointer count value22 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_71.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x153d4 (blobTailState (pointer + BV 64 32)%bv count
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv <> BV 64 0⌝ ∗ True) -∗
  instr_pre 0x15564 (blobTailState (pointer + BV 64 32)%bv count
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv = BV 64 0⌝ ∗ True) -∗
  instr_body 0x15558 (blobTailState pointer count value22 P).
Proof.
  zesu_block.
  all: replace (count - BV 64 1)%bv
    with (count + BV 64 18446744073709551615)%bv by bv_solve; assumption.
Qed.
Print Assumptions blob_tail_pre_correct.
