Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_88 Require Import instrs.

Definition postTransactionsWithdrawalLoadEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old8 old9 olddata : bv 64) (values : list (bv 64))
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x8" ↦ᵣ RVal_Bits old8 ∗ "x9" ↦ᵣ RVal_Bits old9 ∗
   "x10" ↦ᵣ RVal_Bits olddata ∗ (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   ⌜length values = 69%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@postTransactionsWithdrawalLoadEntry) := I.

Definition postTransactionsWithdrawalLoadPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15684) ∗
   "x8" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 11%nat)) ∗
   "x9" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 12%nat)) ∗
   "x10" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 12%nat)) ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   ⌜length values = 69%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@postTransactionsWithdrawalLoadPost) := I.

Lemma post_transactions_exact_withdrawal_load_correct `{!islaG Sigma} `{!threadG}
    sp oldra old8 old9 olddata values (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_88.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15688 (postTransactionsWithdrawalLoadPost sp values P) -∗
  instr_body 0x15678 (postTransactionsWithdrawalLoadEntry sp oldra old8 old9 olddata values P).
Proof.
  zesu_block.
  all: match goal with
  | Hlookup : ?vs !! ?index = Some ?word |- ?word = default _ (?vs !! ?target) =>
      replace index with target in Hlookup by bv_solve;
      rewrite Hlookup; reflexivity
  end.
Qed.
Print Assumptions post_transactions_exact_withdrawal_load_correct.
