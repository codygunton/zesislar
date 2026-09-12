Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128Correct.

Lemma zesu_encoder_u128_payload_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 zesuEncoderU128PayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /zesuEncoderU128PayloadCallSpec.
  iDestruct "Hentry" as (low high sp ret tail)
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & Hnext & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "[H5 %Hr5]".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  iPoseProof (encoder_u128_exact_correct low high sp ret tail True%I
    with "Hcode Houtput") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". rewrite /encoderU128ExactSpec.
  iExists b5. rewrite -writeSuccessU128WordsPayload_encoder.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hnext"); [done | done |].
  iIntros "Hpost". iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hpayload & Hgap & Hra & Hmmio & Htrace & _ & _)".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: lazymatch goal with |- ?G => fail "u128 call residual" G end.
Qed.

Lemma zesu_encoder_u128_payload_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15ce4 zesuEncoderU128PayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_u128_payload_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_u128_payload_call_correct.
Print Assumptions zesu_encoder_u128_payload_call_pre.
