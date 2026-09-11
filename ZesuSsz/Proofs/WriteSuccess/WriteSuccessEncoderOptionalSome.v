Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomePreInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeInt.

Lemma encoder_optional_some_correct `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8
    (encoderOptionalSomeSpec data value sp ret tag tail P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #H04map #H03 #H07 #H01".
  iPoseProof "H04map" as "#H04heads".
  iEval (rewrite /IslaTraces.write_success_04.instrs.instr_map
    big_sepL_cons) in "H04heads".
  iDestruct "H04heads" as "(#Hc8 & #H04tail)".
  iEval (rewrite big_sepL_cons) in "H04tail".
  iDestruct "H04tail" as "(#Hcc & _)".
  iApply (encoder_optional_some_entry with "Hc8").
  iApply (encoder_optional_some_branch with "Hcc").
  iApply (encoder_optional_some_pre_int with "H04map H03 H01").
  iApply (encoder_optional_some_int with "H07 H01").
Qed.
