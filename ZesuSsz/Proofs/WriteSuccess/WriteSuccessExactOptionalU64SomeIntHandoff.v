Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64SomeExactIntFrame `{!islaG Sigma} `{!threadG}
    (old_x8 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ P ∗ True)%I.

Definition optionalU64SomeExactIntEntry `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x8 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits value ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ instr_pre (bv_unsigned ret)
     (encoderIntExactFramedPost sp ret tail (optionalU64SomeExactIntFrame old_x8 P)) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactIntFrame) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactIntEntry) := I.

Lemma optional_u64_some_exact_int_handoff `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x8 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr_body 0x15d10
    (encoderIntExactFramedSpec value sp ret old_x5 old_x11 tail
      (optionalU64SomeExactIntFrame old_x8 P)) -∗
  instr_body 0x15d10
    (optionalU64SomeExactIntEntry value sp ret old_x5 old_x8 old_x11 tail P).
Proof.
  iStartProof. iIntros "Hcallee".
  iApply (instr_pre_wand 0x15d10 0x15d10 false false with "Hcallee");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hs0 & Hra & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  zesu_run.
Qed.

Print Assumptions optional_u64_some_exact_int_handoff.
