From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Some.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64None.

Lemma zesu_encoder_optional_u64_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64CallSpec.
Proof.
  iStartProof.
  iIntros "#Hcode #Hboolean #Hint".
  iPoseProof (zesu_encoder_optional_u64_some_call_correct with
    "Hcode Hboolean Hint") as "HsomeBody".
  iPoseProof (zesu_encoder_optional_u64_none_call_correct with
    "Hcode Hboolean") as "HnoneBody".
  rewrite instr_pre'_eq. iIntros "[Hsome|Hnone]".
  - iApply ("HsomeBody" with "Hsome").
  - iApply ("HnoneBody" with "Hnone").
Qed.

Lemma zesu_encoder_optional_u64_call_pre
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec.
Proof.
  iStartProof.
  iIntros "#HoptionalCode #Hboolean #Hint".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_optional_u64_call_correct; iAssumption.
Qed.
