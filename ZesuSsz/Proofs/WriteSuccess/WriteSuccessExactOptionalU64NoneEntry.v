Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_04 Require Import instrs.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition optionalU64NoneObjectFrame `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ bytes ∗ P ∗ True)%I.

Definition optionalU64NoneExactEntry `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜bytes !! 8%nat = Some (BV 8 0)⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 0)) tail) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderBooleanExactPost (BV 64 0) sp ret tail
       (optionalU64NoneBooleanFrame (optionalU64NoneObjectFrame pointer bytes P))) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64NoneObjectFrame) := I.
Global Instance : LithiumUnfold (@optionalU64NoneExactEntry) := I.

Lemma optional_u64_none_exact_entry `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c04
    (optionalU64NoneExactTailEntry sp ret old_x5 old_x6 pointer (BV 64 0) tail
      (optionalU64NoneObjectFrame pointer bytes P)) -∗
  instr_body 0x15bc8 (optionalU64NoneExactEntry pointer sp ret old_x5 old_x6
    old_x11 bytes tail P).
Proof.
  zesu_block.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try zesu_finish_array_branch.
Qed.

Print Assumptions optional_u64_none_exact_entry.
