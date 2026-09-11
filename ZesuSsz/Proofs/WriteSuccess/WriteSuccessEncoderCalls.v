Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBoolean.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.

Definition zesuEncoderIntAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    encoderIntSpec value sp ret tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntAny) := I.

Lemma zesu_encoder_int_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntAny.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (value sp ret tail) "Hspec".
  iPoseProof (encoder_int_correct value sp ret tail True%I
    with "HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Definition zesuEncoderBytesAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8)) (tail : spec),
    encoderBytesSpec data size sp ret bytes tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBytesAny) := I.

Lemma zesu_encoder_bytes_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesAny.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (data size sp ret bytes tail) "Hspec".
  iPoseProof (encoder_bytes_correct data size sp ret bytes tail True%I
    with "HbytesCode HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Definition zesuEncoderBooleanAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    encoderBooleanSpec value sp ret tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanAny) := I.

Lemma zesu_encoder_boolean_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanAny.
Proof.
  iStartProof. iIntros "#HbooleanCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (value sp ret tail) "Hspec".
  iPoseProof (encoder_boolean_correct value sp ret tail True%I
    with "HbooleanCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.
