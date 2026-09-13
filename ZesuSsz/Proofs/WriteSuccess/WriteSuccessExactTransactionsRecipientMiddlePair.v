Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_32 Require Import instrs.

Definition transactionRecipientMiddlePairEntry `{!islaG Sigma} `{!threadG}
    (sp word : bv 64) (b271 b272 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x29" ↦ᵣ RVal_Bits word ∗
   "x30" ↦ᵣ RVal_Bits (bv_zero_extend 64 b271) ∗
   "x5" ↦ᵣ RVal_Bits (bv_zero_extend 64 b272) ∗
   (bv_unsigned sp + 128) ↦ₘ? 8 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 136 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddlePairEntry) := I.

Definition transactionRecipientMiddlePairPost `{!islaG Sigma} `{!threadG}
    (sp word : bv 64) (b271 b272 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x29" ↦ᵣ RVal_Bits word ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b271 * 65536)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned b271 * 65536 + bv_unsigned b272 * 16777216)) ∗
   (bv_unsigned sp + 128) ↦ₘ word ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 136 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddlePairPost) := I.

Lemma transactions_recipient_middle_pair_correct `{!islaG Sigma} `{!threadG}
    sp word b271 b272 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15038 (transactionRecipientMiddlePairPost sp word b271 b272 P) -∗
  instr_body 0x15028 (transactionRecipientMiddlePairEntry sp word b271 b272 P).
Proof.
  zesu_block.
  all: replace (bv_shiftl (bv_zero_extend 64 b272) (BV 64 24))
    with (Z_to_bv 64 (bv_unsigned b272 * 16777216)) by bv_solve.
  all: replace (bv_shiftl (bv_zero_extend 64 b271) (BV 64 16))
    with (Z_to_bv 64 (bv_unsigned b271 * 65536)) by bv_solve.
  all: apply array_byte_pair_value16.
Qed.
Print Assumptions transactions_recipient_middle_pair_correct.
