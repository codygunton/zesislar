Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeIntHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeResume.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64SomeExactBooleanScratch `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 32) ↦ₘ? 7 ∗
   (bv_unsigned sp - 25) ↦ₘ∗ writeSuccessBooleanWordPayload (BV 64 1) ∗
   (bv_unsigned sp - 24) ↦ₘ (BV 64 0x15bec) ∗ P ∗ True)%I.

Definition optionalU64SomeExactBooleanResumeFrame `{!islaG Sigma} `{!threadG}
    (value sp ret old_x6 old_x8 : bv 64) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits old_x6 ∗ "x8" ↦ᵣ RVal_Bits value ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ instr_pre (bv_unsigned ret)
     (encoderIntExactFramedPost sp ret tail (optionalU64SomeExactIntFrame old_x8
       (optionalU64SomeExactBooleanScratch sp P))) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactBooleanScratch) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactBooleanResumeFrame) := I.

Definition optionalU64SomeExactPost `{!islaG Sigma} `{!threadG}
    (sp ret old_x8 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗ "x8" ↦ᵣ RVal_Bits old_x8 ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactPost) := I.

Lemma optional_u64_some_exact_scratch_cleanup `{!islaG Sigma} `{!threadG}
    (sp ret old_x8 : bv 64) (tail : spec) (P : iProp Sigma) :
  encoderIntExactFramedPost sp ret tail (optionalU64SomeExactIntFrame old_x8
    (optionalU64SomeExactBooleanScratch sp P)) -∗
  optionalU64SomeExactPost sp ret old_x8 tail P.
Proof.
  iStartProof. iIntros "Hpost". iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(H6 & H8 & Hscratch & _)".
  iDestruct "Hscratch" as "(Hlow & Hbyte & Hra & HP & _)".
  zesu_run.
Qed.

Print Assumptions optional_u64_some_exact_scratch_cleanup.

Lemma optional_u64_some_exact_boolean_resume_handoff `{!islaG Sigma} `{!threadG}
    (value sp ret old_x6 old_x8 : bv 64) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15bec (optionalU64SomeExactResumeEntry value sp ret
    (BV 64 (mapIoContextAddress defaultMap)) old_x6 old_x8 (sp - BV 64 25)%bv (BV 64 1) tail
    (optionalU64SomeExactBooleanScratch sp P)) -∗
  instr_body 0x15bec (encoderBooleanExactPost (BV 64 1) (sp - BV 64 16)%bv
    (BV 64 0x15bec)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (optionalU64SomeExactBooleanResumeFrame value sp ret old_x6 old_x8 tail P)).
Proof. move => *. zesu_block. Qed.

Print Assumptions optional_u64_some_exact_boolean_resume_handoff.
