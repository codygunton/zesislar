From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeToBoolean.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoolean.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeResume.

Lemma encoder_optional_some_pre_int `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10
    (encoderOptionalSomeAtInt data value sp ret tag tail P) -∗
  instr_body 0x15bd0
    (encoderOptionalSomeAtSomeBody data value sp ret tag tail P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #H04 #H03 #H01 Hnext".
  iApply (encoder_optional_some_to_boolean with "H04").
  iApply (encoder_optional_some_boolean with "H03 H01").
  iApply (encoder_optional_some_resume with "H04 Hnext").
Qed.
