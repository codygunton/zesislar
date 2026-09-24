Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTactics.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64NoneBoundary.

Lemma zesu_encoder_optional_u64_none_tail
    `{!islaG Sigma} `{!threadG} :
  instr 0x15c04 (Some a15c04) -∗
  instr 0x15c08 (Some a15c08) -∗
  instr 0x15c0c (Some a15c0c) -∗
  instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15c04 zesuEncoderOptionalU64NoneAtTail.
Proof. move => *. zesu_block. Qed.
