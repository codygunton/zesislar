Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_60 Require Import instrs.

Definition storageKeysPairs24Entry `{!islaG Sigma} `{!threadG}
    (a b c d : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 a) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b * 256)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned d * 16777216)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs24Entry) := I.

Definition storageKeysPairs24Post `{!islaG Sigma} `{!threadG}
    (a b c d : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b * 256)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs24Post) := I.

Lemma storage_keys_pairs24_correct `{!islaG Sigma} `{!threadG}
    a b c d (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 (drop 20 IslaTraces.write_success_60.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15340 (storageKeysPairs24Post a b c d P) -∗
  instr_body 0x15338 (storageKeysPairs24Entry a b c d P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_value | apply array_byte_pair_value16].
Qed.
Print Assumptions storage_keys_pairs24_correct.
