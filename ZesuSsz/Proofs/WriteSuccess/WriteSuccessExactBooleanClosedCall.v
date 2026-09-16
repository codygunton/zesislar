Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Definition encoderBooleanClosedReturn `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ writeSuccessBooleanWordPayload value ∗
   (bv_unsigned sp - 16) ↦ₘ? 7 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBooleanClosedReturn) := I.

Definition zesuEncoderBooleanExactCallSpec `{!islaG Sigma} `{!threadG}
    : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload value) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (encoderBooleanClosedReturn value sp ret tail) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanExactCallSpec) := I.

Lemma encoder_boolean_closed_return_to_framed `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  encoderBooleanClosedReturn value sp ret tail ∗ P -∗
  encoderBooleanExactPost value sp ret tail P.
Proof.
  iStartProof. iIntros "[Hreturn HP]".
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iEval (unfold encoderBooleanExactPost).
  iEval (unfold encoderBooleanExactReturnedFrame).
  iDestruct "Hreturn" as
    "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hpayload & Hlow &
      Hmmio & Htrace & _)".
  iFrame.
Qed.

Print Assumptions encoder_boolean_closed_return_to_framed.

Lemma encoder_boolean_framed_return_to_closed
    `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) :
  encoderBooleanExactPost value sp ret tail True%I -∗
  encoderBooleanClosedReturn value sp ret tail.
Proof.
  iStartProof. iIntros "Hreturn".
  iEval (unfold encoderBooleanExactPost) in "Hreturn".
  iEval (unfold encoderBooleanExactReturnedFrame) in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & H1 & H2 & Hra & Hframe & _)".
  iDestruct "Hframe" as
    "(H5 & H10 & H11 & Hpayload & Hlow & Hmmio & Htrace & _ & _)".
  iEval (unfold encoderBooleanClosedReturn).
  iFrame.
Qed.

Print Assumptions encoder_boolean_framed_return_to_closed.

Lemma zesu_encoder_boolean_exact_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c zesuEncoderBooleanExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold zesuEncoderBooleanExactCallSpec) in "Hentry".
  iDestruct "Hentry" as (value sp ret tail)
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & Hnext & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5 H11".
  iDestruct "H5" as (r5) "[H5 %Hr5]".
  iDestruct "H11" as (r11) "[H11 %Hr11]".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  apply valu_has_bits_shape in Hr11 as (b11 & ->).
  iPoseProof (encoder_boolean_exact_framed_correct
    value sp ret b5 b11 tail True%I with "Hcode Houtput") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /encoderBooleanExactSpec /encoderBooleanExactPrefixFrame
    /encoderBooleanExactFacts.
  iFrame. repeat iSplit; try iPureIntro; try assumption; try done.
  all: try (bv_simplify_arith Halign; bv_solve).
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hnext"); [done | done |].
  iIntros "Hreturn".
  iApply encoder_boolean_framed_return_to_closed.
  iExact "Hreturn".
Qed.

Print Assumptions zesu_encoder_boolean_exact_call_correct.

Lemma zesu_encoder_boolean_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_boolean_exact_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_boolean_exact_call_pre.

Lemma encoder_boolean_exact_frame_adapter_from_closed
    `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr_body 0x15b9c zesuEncoderBooleanExactCallSpec -∗
  instr_body 0x15b9c
    (encoderBooleanExactSpec value sp ret old_x5 old_x11 tail P).
Proof.
  iStartProof. iIntros "Hcallee".
  iApply (instr_pre_wand 0x15b9c 0x15b9c false false with "Hcallee");
    [done | done |].
  iIntros "Hentry".
  iEval (unfold encoderBooleanExactSpec) in "Hentry".
  iEval (unfold encoderBooleanExactPrefixFrame) in "Hentry".
  iEval (unfold encoderBooleanExactFacts) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H10 & Hstack & %Halign16 & %Halign8 & %Hmin &
      %Hmax & Hframe & _)".
  iDestruct "Hframe" as "(H5 & H11 & Hmmio & Htrace & Hfacts & _)".
  iDestruct "Hfacts" as
    "(%Halign8' & %Hmin' & %Hmax' & %Hret0 & %Hret1 & %Hret2 & HP &
      Hnext & _)".
  iEval (unfold zesuEncoderBooleanExactCallSpec).
  iExists value, sp, ret, tail.
  iFrame.
  iSplitL "H5".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists (RVal_Bits old_x5). iFrame. done. }
  iSplitL "H11".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists (RVal_Bits old_x11). iFrame. done. }
  repeat iSplit; try iPureIntro; try assumption; try done.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hnext"); [done | done |].
  iIntros "Hreturn".
  iApply encoder_boolean_closed_return_to_framed.
  iFrame.
Qed.

Print Assumptions encoder_boolean_exact_frame_adapter_from_closed.

Lemma encoder_boolean_exact_framed_correct_from_closed
    `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c
    (encoderBooleanExactSpec value sp ret old_x5 old_x11 tail P).
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  iApply encoder_boolean_exact_frame_adapter_from_closed.
  iApply (zesu_encoder_boolean_exact_call_correct with "Hcode Houtput").
Qed.

Print Assumptions encoder_boolean_exact_framed_correct_from_closed.
