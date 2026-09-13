Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
From IslaTraces.write_success_04 Require Import a15be8.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma optional_u64_some_exact_payload (value : bv 64) :
  writeSuccessBooleanWordPayload (BV 64 1) ++
    writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)) =
  writeSuccessPrivateBytes
    (writeSuccessEncodeOptional writeSuccessEncodeU64 (Some (bv_unsigned value))).
Proof. reflexivity. Qed.

Print Assumptions optional_u64_some_exact_payload.

Definition optionalU64SomeExactBooleanJumpEntry `{!islaG Sigma} `{!threadG}
    (callee_sp old_x5 old_x11 : bv 64) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15be4) ∗
   "x2" ↦ᵣ RVal_Bits callee_sp ∗ "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
   (bv_unsigned callee_sp - 16) ↦ₘ? 16 ∗
   ⌜bv_extract 0 4 callee_sp = BV 4 0⌝ ∗
   ⌜bv_extract 0 3 callee_sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned callee_sp - 16⌝ ∗
   ⌜bv_unsigned callee_sp < 0x40000000⌝ ∗
   encoderBooleanExactPrefixFrame (BV 64 1) callee_sp (BV 64 0x15bec)
     old_x5 old_x11 tail P ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactBooleanJumpEntry) := I.

Lemma optional_u64_some_exact_boolean_jump `{!islaG Sigma} `{!threadG}
    (callee_sp old_x5 old_x11 : bv 64) (tail : spec)
    (P : iProp Sigma) :
  instr 0x15be8 (Some a15be8) -∗
  instr_body 0x15b9c
    (encoderBooleanExactSpec (BV 64 1) callee_sp (BV 64 0x15bec)
      old_x5 old_x11 tail P) -∗
  instr_body 0x15be8
    (optionalU64SomeExactBooleanJumpEntry callee_sp old_x5 old_x11 tail P).
Proof. zesu_block. Qed.

Print Assumptions optional_u64_some_exact_boolean_jump.
