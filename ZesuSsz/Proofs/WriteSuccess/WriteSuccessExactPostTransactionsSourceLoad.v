Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_87 Require Import instrs.

Definition postTransactionsSourceLoadEntry `{!islaG Sigma} `{!threadG}
    (sp oldra olddata oldsize : bv 64) (values : list (bv 64))
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x10" ↦ᵣ RVal_Bits olddata ∗
   "x11" ↦ᵣ RVal_Bits oldsize ∗ (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   ⌜length values = 69%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@postTransactionsSourceLoadEntry) := I.

Definition postTransactionsSourceLoadPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
   "x10" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 9%nat)) ∗
   "x11" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 10%nat)) ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   ⌜length values = 69%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@postTransactionsSourceLoadPost) := I.

Lemma post_transactions_exact_source_load_correct `{!islaG Sigma} `{!threadG}
    sp oldra olddata oldsize values (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 3 IslaTraces.write_success_87.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15674 (postTransactionsSourceLoadPost sp values P) -∗
  instr_body 0x15668 (postTransactionsSourceLoadEntry sp oldra olddata oldsize values P).
Proof.
  zesu_block.
  all: match goal with
  | Hlookup : ?vs !! ?index = Some ?word |- ?word = default _ (?vs !! ?target) =>
      replace index with target in Hlookup by bv_solve;
      rewrite Hlookup; reflexivity
  end.
Qed.
Print Assumptions post_transactions_exact_source_load_correct.
