Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Lemma zesu_encoder_boolean_exact_payload_call_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (zesuEncoderBooleanExactPayloadCallSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iDestruct "Hentry" as (present sp ret tail)
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5 H11".
  iDestruct "H5" as (r5) "[H5 %Hr5]".
  iDestruct "H11" as (r11) "[H11 %Hr11]".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  apply valu_has_bits_shape in Hr11 as (b11 & ->).
  iPoseProof (encoder_boolean_exact_framed_correct
    (if present then BV 64 1 else BV 64 0) sp ret b5 b11 tail P
    with "Hcode Houtput") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". rewrite /encoderBooleanExactSpec /encoderBooleanExactPrefixFrame
    /encoderBooleanExactFacts writeSuccessBooleanWordPayload_encoder.
  iFrame. iSplitL "H10".
  { destruct present; iExact "H10". }
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hnext"); [done | done |].
  iIntros "Hpost". iDestruct "Hpost" as "(Hsys & H1 & H2 & Hra & Hframe & _)".
  iEval (rewrite /encoderBooleanExactReturnedFrame /writeSuccessBooleanWordPayload
    mem_mapsto_array_singleton) in "Hframe".
  iDestruct "Hframe" as "(H5 & H10 & H11 & Hbyte & Hlow & Hmmio & Htrace & HP & _)".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: lazymatch goal with |- ?G => fail "Boolean call residual" G end.
Qed.

Lemma zesu_encoder_boolean_exact_payload_call_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c (zesuEncoderBooleanExactPayloadCallSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_boolean_exact_payload_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_boolean_exact_payload_call_correct.
Print Assumptions zesu_encoder_boolean_exact_payload_call_pre.
