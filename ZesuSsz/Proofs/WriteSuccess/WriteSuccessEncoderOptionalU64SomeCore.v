From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeEntry.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBranch.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomeBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomeFrame.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomeIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomePublicResumeLeaf.

Lemma zesu_encoder_optional_u64_some_core
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (tail : spec)
    (r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre' true 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre' true 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15bc8
    (encoderOptionalSomeSpec data value sp ret tag tail
      (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
        r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)).
Proof.
  iStartProof. iIntros "#Hcode #Hboolean #Hint".
  iPoseProof (zesu_encoder_optional_u64_some_int_pre with "Hint") as "HintCall".
  iPoseProof (encoder_optional_some_public_resume with "Hcode HintCall")
    as "Hresume".
  iPoseProof (zesu_encoder_optional_u64_some_boolean_call with
    "Hcode Hboolean Hresume") as "HsomeBody".
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hc8 & #Hcc & #Hd0 & #Hd4 & #Hd8 & #Hdc & #He0 & #He4 &
      #He8 & #Hec & #Hf0 & #Hf4 & #Hf8 & #Hfc & #H00 & #H04 &
      #H08 & #H0c & _)".
  iApply (encoder_optional_some_entry with "Hc8").
  iApply (encoder_optional_some_branch with "Hcc HsomeBody").
Qed.

Lemma zesu_encoder_optional_u64_some_core_family
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  ∀ (data value sp ret : bv 64) (tag : bv 8) (tail : spec)
    (r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64),
    instr_body 0x15bc8
      (encoderOptionalSomeSpec data value sp ret tag tail
        (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
          r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)).
Proof.
  iStartProof. iIntros "#Hcode #Hboolean #Hint".
  iIntros (data value sp ret tag tail r9 r12 r13 r14 r15 r16 r17
    r18 r19 r20 r21 r22 r23 r24 r25 r26 r27).
  iApply zesu_encoder_optional_u64_some_core; iAssumption.
Qed.
