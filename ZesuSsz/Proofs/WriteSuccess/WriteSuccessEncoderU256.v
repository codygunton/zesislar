Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Prologue.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Output.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Epilogue.

Lemma zesu_encoder_u256_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈
    IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15cb0 zesuEncoderU256CallSpec.
Proof.
  move => * /=.
  iStartProof.
  iIntros "_ #Hcode #Houtput".
  iDestruct "Hcode" as
    "(#H00 & #H04 & #H08 & #H0c & #H10 & #H14 & #H18 & #H1c &
      #H20 & #H24 & #H28 & #H2c & #H30 & _)".
  iApply (zesu_encoder_u256_prologue with
    "H00 H04 H08 H0c H10 H14").
  iApply (zesu_encoder_u256_output_call with
    "H18 H1c H20 H24 Houtput").
  iApply (zesu_encoder_u256_epilogue with "H28 H2c H30").
Qed.

Lemma zesu_encoder_u256_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈
    IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_u256_call_correct; iAssumption.
Qed.
