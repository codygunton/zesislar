Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomePrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanJump.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanResume.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64SomeExactSourceFrame `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ bytes ∗ P ∗ True)%I.

Definition optionalU64SomeExactCallContext `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 1))
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ instr_pre (bv_unsigned ret)
     (optionalU64SomeExactPost sp ret old_x8 tail
       (optionalU64SomeExactSourceFrame pointer bytes P)) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactSourceFrame) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactCallContext) := I.

Lemma optional_u64_some_exact_jump_handoff `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15be8 (optionalU64SomeExactBooleanJumpEntry (sp - BV 64 16)%bv
    old_x5 old_x11
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (optionalU64SomeExactBooleanResumeFrame value sp ret old_x6 old_x8 tail
      (optionalU64SomeExactSourceFrame pointer bytes P))) -∗
  instr_body 0x15bec (encoderBooleanExactPost (BV 64 1) (sp - BV 64 16)%bv
    (BV 64 0x15bec)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (optionalU64SomeExactBooleanResumeFrame value sp ret old_x6 old_x8 tail
      (optionalU64SomeExactSourceFrame pointer bytes P))) -∗
  instr_body 0x15be8 (optionalU64SomeExactPrefixPost pointer value sp ret old_x8
    old_x11 bytes (optionalU64SomeExactCallContext pointer value sp ret old_x5
      old_x6 old_x8 bytes tail P)).
Proof.
  iStartProof. iIntros "Hjump Hresume".
  iApply (instr_pre_wand 0x15be8 0x15be8 false false with "Hjump");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H8 & H10 & H11 & Hsource & Hlow & Hs0 & Hra & Hcontext & _)".
  iDestruct "Hcontext" as
    "(H5 & H6 & Hmmio & Htrace & %Hsp4 & %Halign & %Hmin & %Hmax &
      %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  zesu_run.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try (bv_simplify Hsp4; bv_solve).
Qed.

Print Assumptions optional_u64_some_exact_jump_handoff.
