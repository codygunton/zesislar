Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.

Definition zesuEncoderU256PayloadCallSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∃ (w0 w1 w2 w3 sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits w0 ∗ "x11" ↦ᵣ RVal_Bits w1 ∗
    "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessPrivateBytes (writeSuccessEncodeU256
        (bv_unsigned w0 + 2 ^ 64 *
          (bv_unsigned w1 + 2 ^ 64 *
            (bv_unsigned w2 + 2 ^ 64 * bv_unsigned w3))))) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
       "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
       (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
       spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderU256PayloadCallSpec) := I.

Lemma zesu_encoder_u256_payload_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cb0 zesuEncoderU256PayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /zesuEncoderU256PayloadCallSpec.
  iDestruct "Hentry" as (w0 w1 w2 w3 sp ret tail)
    "(Hsys & H1 & H2 & H5 & H10 & H11 & H12 & H13 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & Hnext & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "[H5 %Hr5]".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  iPoseProof (encoder_u256_exact_correct w0 w1 w2 w3 sp ret tail True%I
    with "Hcode Houtput") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". rewrite /encoderU256ExactSpec.
  iExists b5. rewrite -writeSuccessU256WordsPayload_encoder. iFrame.
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hnext"); [done | done |].
  iIntros "Hpost". iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hra & Hmmio & Htrace & _ & _)".
  zesu_run.
Qed.

Lemma zesu_encoder_u256_payload_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15cb0 zesuEncoderU256PayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_u256_payload_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_u256_payload_call_correct.
Print Assumptions zesu_encoder_u256_payload_call_pre.
