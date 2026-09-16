Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicRawReturnSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicRawPrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicRawReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessInstrBodyAdapters.
From IslaTraces.write_success_05 Require Import instrs.

Lemma byte_lists_exact_public_prefix_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  instr_body 0x15c34 byteListsExactPublicCountReturnSpec -∗
  instr_body 0x15c10 encoderByteListsExactCallSpec.
Proof.
  iIntros "#Hcode #Hint Hnext".
  iApply (byte_lists_exact_public_raw_prefix_correct with "Hcode Hint [Hnext]").
  iApply (instr_body_wand_adapter 0x15c34
    byteListsExactPublicCountReturnSpec byteListsExactPublicRawCountReturnSpec
    with "[] Hnext").
  iIntros "Hraw".
  iApply (byte_lists_exact_public_raw_count_return_resources with "Hcode Hraw").
Qed.
Print Assumptions byte_lists_exact_public_prefix_correct.
