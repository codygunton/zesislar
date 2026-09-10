From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalNoneBoundaries.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalNoneEntry.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalNoneTail.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalNoneBoolean.

Import ListNotations.

Lemma encoder_optional_none_correct `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (encoderOptionalNoneSpec data value sp ret tail P).
Proof.
  iStartProof. iIntros "#H04 #H03 #H07 #H01".
  iPoseProof "H04" as "#H04heads".
  iEval (rewrite /IslaTraces.write_success_04.instrs.instr_map big_sepL_cons)
    in "H04heads".
  iDestruct "H04heads" as "(#Hc8 & H04tail)".
  iEval (rewrite big_sepL_cons) in "H04tail".
  iDestruct "H04tail" as "(#Hcc & H04tail)".
  do 13 (iEval (rewrite big_sepL_cons) in "H04tail";
         iDestruct "H04tail" as "(_ & H04tail)").
  iEval (rewrite big_sepL_cons) in "H04tail".
  iDestruct "H04tail" as "(#Hc04 & H04tail)".
  iEval (rewrite big_sepL_cons) in "H04tail".
  iDestruct "H04tail" as "(#Hc08 & H04tail)".
  iEval (rewrite big_sepL_cons) in "H04tail".
  iDestruct "H04tail" as "(#Hc0c & _)".
  iPoseProof (encoder_optional_none_boolean data value sp ret tail P
    with "H03 H01") as "Hboolean".
  iAssert (instr_pre 0x15b9c
    (encoderOptionalNoneAtBoolean data value sp ret tail P))%I
    with "[Hboolean]" as "Hboolean_pre".
  { iApply instr_pre_to_body. iNext. iExact "Hboolean". }
  iPoseProof (encoder_optional_none_tail data value sp ret tail P with
    "Hc04 Hc08 Hc0c Hboolean_pre") as "Htail".
  iApply (encoder_optional_none_entry data value sp ret tail P with
    "Hc8 Hcc Htail").
Qed.
