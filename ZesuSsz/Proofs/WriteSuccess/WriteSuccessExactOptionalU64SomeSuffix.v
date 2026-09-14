Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_04 Require Import instrs.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition optionalU64SomeExactSuffixPost `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x8 old_x11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits value ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   P ∗ True)%I.

Definition optionalU64SomeExactSuffixEntry `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x6 old_x8 old_x10 old_x11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15bec) ∗
   "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x8" ↦ᵣ RVal_Bits value ∗ "x10" ↦ᵣ RVal_Bits old_x10 ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   P ∗ instr_pre 0x15d10
     (optionalU64SomeExactSuffixPost value sp ret old_x5 old_x8 old_x11 P) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactSuffixPost) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactSuffixEntry) := I.

Lemma optional_u64_some_exact_suffix `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x6 old_x8 old_x10 old_x11 : bv 64)
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 (drop 9 IslaTraces.write_success_04.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bec
    (optionalU64SomeExactSuffixEntry value sp ret old_x5 old_x6 old_x8
      old_x10 old_x11 P).
Proof.
  zesu_block.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try (bv_simplify select (bv_extract 0 4 sp = _); bv_solve).
Qed.

Print Assumptions optional_u64_some_exact_suffix.
