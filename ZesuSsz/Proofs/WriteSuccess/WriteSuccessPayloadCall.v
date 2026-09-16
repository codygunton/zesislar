Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Import ListNotations.

(** This ABI contract exposes one fixed output payload to native callers. *)
Definition zesuWriteOutputPayloadCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 0 (fun args _ RET => ∃ (payload : list (bv 8)) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ∗ payload ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (args !!! 0%nat) (args !!! 1%nat) payload tail) ∗
    ⌜Z.to_N (bv_unsigned (args !!! 1%nat)) = N.of_nat (length payload)⌝ ∗
    RET (fun _ => bv_unsigned (args !!! 0%nat) ↦ₘ∗ payload ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuWriteOutputPayloadCallSpec) := I.

Lemma zesu_write_output_payload_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 zesuWriteOutputPayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode". rewrite instr_pre'_eq. iIntros "Hspec".
  iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call) in "Hspec". iDestruct "Hspec" as (sp ret) "(Hsys & Htmp & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)". iDestruct "Hrest" as (b10) "[%Hb10 Hrest]". subst r10.
  iDestruct "Hrest" as (r11) "[H11 Hrest]". iDestruct "Hrest" as (b11) "[%Hb11 Hrest]". subst r11.
  iDestruct "Hrest" as (r12) "[H12 Hrest]". iDestruct "Hrest" as (b12) "[%Hb12 Hrest]". subst r12.
  iDestruct "Hrest" as (r13) "[H13 Hrest]". iDestruct "Hrest" as (b13) "[%Hb13 Hrest]". subst r13.
  iDestruct "Hrest" as (r14) "[H14 Hrest]". iDestruct "Hrest" as (b14) "[%Hb14 Hrest]". subst r14.
  iDestruct "Hrest" as (r15) "[H15 Hrest]". iDestruct "Hrest" as (b15) "[%Hb15 Hrest]". subst r15.
  iDestruct "Hrest" as (r16) "[H16 Hrest]". iDestruct "Hrest" as (b16) "[%Hb16 Hrest]". subst r16.
  iDestruct "Hrest" as (r17) "[H17 Hrest]". iDestruct "Hrest" as (b17) "[%Hb17 Hrest]". subst r17.
  iDestruct "Hrest" as (r8) "(H8 & %Hr8 & Hrest)". iDestruct "Hrest" as (r9) "(H9 & %Hr9 & Hrest)".
  iDestruct "Hrest" as (r18) "(H18 & %Hr18 & Hrest)". iDestruct "Hrest" as (r19) "(H19 & %Hr19 & Hrest)".
  iDestruct "Hrest" as (r20) "(H20 & %Hr20 & Hrest)". iDestruct "Hrest" as (r21) "(H21 & %Hr21 & Hrest)".
  iDestruct "Hrest" as (r22) "(H22 & %Hr22 & Hrest)". iDestruct "Hrest" as (r23) "(H23 & %Hr23 & Hrest)".
  iDestruct "Hrest" as (r24) "(H24 & %Hr24 & Hrest)". iDestruct "Hrest" as (r25) "(H25 & %Hr25 & Hrest)".
  iDestruct "Hrest" as (r26) "(H26 & %Hr26 & Hrest)". iDestruct "Hrest" as (r27) "(H27 & %Hr27 & Hrest)".
  iDestruct "Hrest" as "(H1 & H2 & %Hspalign & %Hret0 & %Hret1 & %Hret2 & %Hstackbounds & Hstack & Hrest)".
  iDestruct "Hrest" as (payload tail) "(Hpayload & Hmmio & Htrace & %Hsize & Hret)".
  iEval (rewrite /tmp_registers !reg_col_cons reg_col_nil) in "Htmp". iDestruct "Htmp" as "(H5 & Htmp)".
  iDestruct "H5" as (v5 Hv5) "H5". apply valu_has_bits_shape in Hv5 as (b5 & ->).
  set (P := (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x6"; "x7"; "x28"; "x29"; "x30"; "x31"]) ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗ "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗ "x8" ↦ᵣ r8 ∗ "x9" ↦ᵣ r9 ∗ "x18" ↦ᵣ r18 ∗
    "x19" ↦ᵣ r19 ∗ "x20" ↦ᵣ r20 ∗ "x21" ↦ᵣ r21 ∗ "x22" ↦ᵣ r22 ∗ "x23" ↦ᵣ r23 ∗ "x24" ↦ᵣ r24 ∗
    "x25" ↦ᵣ r25 ∗ "x26" ↦ᵣ r26 ∗ "x27" ↦ᵣ r27 ∗ "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp - 0) ↦ₘ? 0)%I).
  iPoseProof (write_output_trace_correct b10 b11 ret payload tail P with "Hcode") as "Hbody".
  rewrite instr_pre'_eq. iApply "Hbody". iExists b5. iFrame "Hsys H1 H5 H10 H11 Hpayload Hmmio Htrace".
  iSplit; first (iPureIntro; exact Hsize). iSplit; first (iPureIntro; exact Hret0).
  iSplit; first (iPureIntro; exact Hret1). iSplit; first (iPureIntro; exact Hret2).
  iSplitL "Htmp H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H2 Hstack".
  { subst P. iFrame. done. }
  iSplit; last done. rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hpayload & Hmmio & Htrace & HP & _)". subst P.
  iDestruct "HP" as "(Htmp & H12 & H13 & H14 & H15 & H16 & H17 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H2 & Hstack)".
  iApply "Hret". liARun.
Qed.

Lemma zesu_write_output_payload_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro. iApply instr_pre_to_body. iNext.
  iApply zesu_write_output_payload_call_correct. iExact "Hcode".
Qed.

Print Assumptions zesu_write_output_payload_call_pre.
