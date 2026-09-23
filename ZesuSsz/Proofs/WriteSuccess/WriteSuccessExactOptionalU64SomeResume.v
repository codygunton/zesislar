Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeIntHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeSuffix.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64SomeExactResumeContext `{!islaG Sigma} `{!threadG}
    (value sp ret old_x8 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ instr_pre (bv_unsigned ret)
     (encoderIntExactFramedPost sp ret tail (optionalU64SomeExactIntFrame old_x8 P)) ∗ True)%I.

Definition optionalU64SomeExactResumeEntry `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x6 old_x8 old_x10 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15bec) ∗ "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x8" ↦ᵣ RVal_Bits value ∗ "x10" ↦ᵣ RVal_Bits old_x10 ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   optionalU64SomeExactResumeContext value sp ret old_x8 tail P ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactResumeContext) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactResumeEntry) := I.

Lemma optional_u64_some_exact_resume_handoff `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x8 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr_body 0x15d10
    (optionalU64SomeExactIntEntry value sp ret old_x5 old_x8 old_x11 tail P) -∗
  instr_body 0x15d10 (optionalU64SomeExactSuffixPost value sp ret old_x5 old_x8
    old_x11 (optionalU64SomeExactResumeContext value sp ret old_x8 tail P)).
Proof. move => *. zesu_block. Qed.

Lemma optional_u64_some_exact_resume `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x6 old_x8 old_x10 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 (drop 9 IslaTraces.write_success_04.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bec (optionalU64SomeExactResumeEntry value sp ret old_x5 old_x6
    old_x8 old_x10 old_x11 tail P).
Proof.
  iStartProof. iIntros "#Hsuffix #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct value sp ret old_x5 old_x11 tail
    (optionalU64SomeExactIntFrame old_x8 P) with "Hencoder Houtput") as "HencoderBody".
  iPoseProof (optional_u64_some_exact_int_handoff with "HencoderBody") as "Htail".
  iPoseProof (optional_u64_some_exact_resume_handoff with "Htail") as "Hresume".
  iPoseProof (optional_u64_some_exact_suffix value sp ret old_x5 old_x6 old_x8
    old_x10 old_x11 (optionalU64SomeExactResumeContext value sp ret old_x8 tail P)
    with "Hsuffix") as "Hbody".
  iApply (instr_pre_wand 0x15bec 0x15bec false false with "Hbody");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hs0 & Hra & %Hsp4 & Hcontext & _)".
  iDestruct "Hcontext" as
    "(Hmmio & Htrace & %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 &
      HP & Hnext & _)".
  zesu_run.
Qed.

Print Assumptions optional_u64_some_exact_resume_handoff.
Print Assumptions optional_u64_some_exact_resume.
