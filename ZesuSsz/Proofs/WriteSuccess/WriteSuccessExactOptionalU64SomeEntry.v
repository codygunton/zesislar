Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomePrefix.
From IslaTraces.write_success_04 Require Import instrs.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition optionalU64SomeExactEntry `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜bytes !! 8%nat = Some tag⌝ ∗ ⌜tag <> BV 8 0⌝ ∗
   ⌜value = Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))⌝ ∗
   ⌜(8 <= length bytes)%nat⌝ ∗ ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   P ∗ instr_pre 0x15be8
     (optionalU64SomeExactPrefixPost pointer value sp ret old_x8
       (bv_zero_extend 64 tag) bytes P) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactEntry) := I.

Lemma optional_u64_some_exact_entry `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bd0 (optionalU64SomeExactPrefixEntry pointer value sp ret old_x8
    (bv_zero_extend 64 tag) bytes P) -∗
  instr_body 0x15bc8
    (optionalU64SomeExactEntry pointer value sp ret old_x8 old_x11 tag bytes P).
Proof.
  zesu_block.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try zesu_finish_array_branch.
Qed.

Print Assumptions optional_u64_some_exact_entry.

Lemma optional_u64_some_exact_entry_to_boolean_jump `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 6 (drop 2 IslaTraces.write_success_04.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8
    (optionalU64SomeExactEntry pointer value sp ret old_x8 old_x11 tag bytes P).
Proof.
  iStartProof. iIntros "#Hbranch #Hprefix".
  iApply (optional_u64_some_exact_entry with "Hbranch").
  iApply (optional_u64_some_exact_prefix with "Hprefix").
Qed.

Print Assumptions optional_u64_some_exact_entry_to_boolean_jump.
