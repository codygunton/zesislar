Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64SomePublicResume.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_optional_some_public_resume
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x15d10
    (encoderOptionalSomeAtPublicInt data value sp ret tag tail P) -∗
  instr_body 0x15bec
    (encoderOptionalSomeAtPublicResume data value sp ret tag tail P).
Proof. move => *. zesu_block. Qed.
