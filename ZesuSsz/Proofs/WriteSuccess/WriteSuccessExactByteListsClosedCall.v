Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_05 Require Import instrs.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.

(** The exact byte-list contract is already closed in the B2 call shape.
    Its [zesu_c_call] expansion quantifies [ret : bv 64], fixes the caller
    resources, exposes [tail] through [spec_trace], and ends in
    [instr_pre (bv_unsigned ret) (zesu_c_call_ret ...)]. *)
Definition zesuEncoderByteListsExactCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  encoderByteListsExactCallSpec.

Global Instance : LithiumUnfold (@zesuEncoderByteListsExactCallSpec) := I.

Lemma encoder_byte_lists_exact_closed_equiv
    `{!islaG Sigma} `{!threadG} :
  zesuEncoderByteListsExactCallSpec ⊣⊢ encoderByteListsExactCallSpec.
Proof. rewrite /zesuEncoderByteListsExactCallSpec. done. Qed.

Print Assumptions encoder_byte_lists_exact_closed_equiv.

Lemma encoder_byte_lists_exact_body_from_framed
    `{!islaG Sigma} `{!threadG} :
  instr_body 0x15c10 encoderByteListsExactCallSpec -∗
  instr_body 0x15c10 zesuEncoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "Hbody".
  rewrite /zesuEncoderByteListsExactCallSpec. iExact "Hbody".
Qed.

Print Assumptions encoder_byte_lists_exact_body_from_framed.

Lemma zesu_encoder_byte_lists_exact_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c10 zesuEncoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hlists #Hbytes #Hint #Houtput".
  iApply encoder_byte_lists_exact_body_from_framed.
  iApply (byte_lists_exact_correct with "Hlists").
  - iApply (zesu_encoder_int_payload_call_pre with "Hint Houtput").
  - iApply (encoder_bytes_exact_call_pre with "Hbytes Hint Houtput").
Qed.

Print Assumptions zesu_encoder_byte_lists_exact_call_correct.

Lemma zesu_encoder_byte_lists_exact_call_pre
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hlists #Hbytes #Hint #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (zesu_encoder_byte_lists_exact_call_correct with
    "Hlists Hbytes Hint Houtput").
Qed.

Print Assumptions zesu_encoder_byte_lists_exact_call_pre.
