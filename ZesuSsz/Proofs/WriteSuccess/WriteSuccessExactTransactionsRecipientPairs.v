Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionRecipientPairsEntry `{!islaG Sigma} `{!threadG}
    (b283 b284 b273 b274 b275 b276 b277 b278 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col [(KindReg "x15", BitsShape 64)] ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b283 * 65536)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b284 * 16777216)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b274 * 256)) ∗
   "x6" ↦ᵣ RVal_Bits (bv_zero_extend 64 b273) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b276 * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b275 * 65536)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b278 * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (bv_zero_extend 64 b277) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairsEntry) := I.

Definition transactionRecipientPairsPost `{!islaG Sigma} `{!threadG}
    (b283 b284 b273 b274 b275 b276 b277 b278 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned b283 * 65536 + bv_unsigned b284 * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b273 + bv_unsigned b274 * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned b275 * 65536 + bv_unsigned b276 * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b277 + bv_unsigned b278 * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b274 * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b276 * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b275 * 65536)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b278 * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (bv_zero_extend 64 b277) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairsPost) := I.

Lemma transactions_recipient_pairs_correct `{!islaG Sigma} `{!threadG}
    b283 b284 b273 b274 b275 b276 b277 b278 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fe0
    (transactionRecipientPairsPost b283 b284 b273 b274 b275 b276 b277 b278 P) -∗
  instr_body 0x14fd0
    (transactionRecipientPairsEntry b283 b284 b273 b274 b275 b276 b277 b278 P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_value | apply array_byte_pair_value16].
Qed.
Print Assumptions transactions_recipient_pairs_correct.
