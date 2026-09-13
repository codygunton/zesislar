Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicPrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicCountReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_05 Require Import instrs.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.

Lemma byte_lists_exact_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  instr_body 0x15c10 encoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hint #Hbytes".
  iPoseProof (byte_lists_exact_public_count_return_correct with "Hcode Hbytes") as "Hnext".
  iApply (byte_lists_exact_public_prefix_correct with "Hcode Hint Hnext").
Qed.
Print Assumptions byte_lists_exact_correct.

Lemma byte_lists_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  □ instr_pre 0x15c10 encoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hint #Hbytes". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply byte_lists_exact_correct; iAssumption.
Qed.
Print Assumptions byte_lists_exact_call_pre.

Lemma byte_lists_exact_native_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c10 encoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hlists #Hbytes #Hint #Houtput".
  iPoseProof (zesu_encoder_int_payload_call_pre with "Hint Houtput") as "#HintPre".
  iPoseProof (encoder_bytes_exact_call_pre with "Hbytes Hint Houtput") as "#HbytesPre".
  iApply (byte_lists_exact_call_pre with "Hlists HintPre HbytesPre").
Qed.
Print Assumptions byte_lists_exact_native_pre.
