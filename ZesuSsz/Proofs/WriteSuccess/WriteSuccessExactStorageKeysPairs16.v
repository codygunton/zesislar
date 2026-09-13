Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_59 Require Import instrs.

Definition storageKeysPairs16Entry `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (bv_zero_extend 64 a) ∗
   "x7" ↦ᵣ RVal_Bits (bv_zero_extend 64 b) ∗
   "x28" ↦ᵣ RVal_Bits (bv_zero_extend 64 c) ∗
   "x1" ↦ᵣ RVal_Bits (bv_zero_extend 64 d) ∗
   "x8" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x26" ↦ᵣ RVal_Bits (bv_zero_extend 64 f) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs16Entry) := I.

Definition storageKeysPairs16Post `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned d * 16777216)) ∗
   "x8" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned f * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs16Post) := I.

Lemma storage_keys_pairs16_correct `{!islaG Sigma} `{!threadG}
    a b c d e f (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 7 IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x152a4 (storageKeysPairs16Post a b c d e f P) -∗
  instr_body 0x15288 (storageKeysPairs16Entry a b c d e f P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_shift_value | apply array_byte_pair_shift_value16].
Qed.
Print Assumptions storage_keys_pairs16_correct.
