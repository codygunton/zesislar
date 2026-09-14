Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
From IslaTraces.write_success_04 Require Import instrs.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma optional_u64_none_exact_payload :
  writeSuccessBooleanWordPayload (BV 64 0) =
  writeSuccessPrivateBytes (writeSuccessEncodeOptional writeSuccessEncodeU64 None).
Proof. reflexivity. Qed.

Definition optionalU64NoneBooleanFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits (BV 64 0x15c08) ∗ P ∗ True)%I.

Definition optionalU64NoneExactTailEntry `{!islaG Sigma} `{!threadG}
    (sp ret old_x5 old_x6 old_x10 old_x11 : bv 64) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 0)) tail) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderBooleanExactPost (BV 64 0) sp ret tail
       (optionalU64NoneBooleanFrame P)) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64NoneBooleanFrame) := I.
Global Instance : LithiumUnfold (@optionalU64NoneExactTailEntry) := I.

Lemma optional_u64_none_exact_tail `{!islaG Sigma} `{!threadG}
    (sp ret old_x5 old_x6 old_x10 old_x11 : bv 64) (tail : spec)
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 15 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (encoderBooleanExactSpec (BV 64 0) sp ret old_x5 old_x11
    tail (optionalU64NoneBooleanFrame P)) -∗
  instr_body 0x15c04
    (optionalU64NoneExactTailEntry sp ret old_x5 old_x6 old_x10 old_x11 tail P).
Proof.
  zesu_block.
  Unshelve. all: try zesu_finish.
Qed.

Print Assumptions optional_u64_none_exact_tail.
Print Assumptions optional_u64_none_exact_payload.
