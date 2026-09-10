Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_116 Require Import a15960.
From IslaTraces.write_success_116 Require Import a15964.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessInstrBodyAdapters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixInt15968Call.

Definition writeSuccessSuffixInt15960To1596cSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 64) ↦ₘ value ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 64 < 0x40000000⌝ ∗
    instr_pre 0x1596c (writeSuccessSuffixInt1596cCallPost sp tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixInt15960To1596cSpec) := I.

Definition writeSuccessSuffixInt15960Frame
    `{!islaG Sigma} `{!threadG} (tail : spec) (Q : iProp Sigma)
    (base : bv 64) : iProp Sigma :=
  ("x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   (bv_unsigned base - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (base - BV 64 16)%bv (BV 64 8) tail) ∗
   instr_pre 0x1596c (writeSuccessSuffixInt1596cCallPost base tail ∗ Q) ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15960Frame) := I.

Definition writeSuccessSuffixInt15960RawSpec
    `{!islaG Sigma} `{!threadG} (K : bv 64 -> spec -> iProp Sigma) : iProp Sigma :=
  (∃ (value base : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 64) ↦ₘ value ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base + 64 < 0x40000000⌝ ∗
    K base tail ∗
    instr_pre 0x15964
      (reg_col zesu_ram_sys_regs ∗
       "x10" ↦ᵣ RVal_Bits value ∗
       "x2" ↦ᵣ RVal_Bits base ∗
       (bv_unsigned base + 64) ↦ₘ value ∗ K base tail))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15960RawSpec) := I.

Lemma write_success_suffix_int_15960_raw
    `{!islaG Sigma} `{!threadG} (K : bv 64 -> spec -> iProp Sigma) :
  instr 0x15960 (Some IslaTraces.write_success_116.a15960.a15960) -∗
  instr_body 0x15960 (writeSuccessSuffixInt15960RawSpec K).
Proof.
  iStartProof. iIntros "Hinstr".
  iApply (instr_pre_intro_Some with "Hinstr").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt15960RawSpec) in "Hentry".
  iDestruct "Hentry" as (value base tail)
    "(Hsys & H10 & H2 & Hvalue & %Halign & %Hrange & HK & Hnext)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & %Hshape10)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try iFrame.
Qed.

Lemma write_success_suffix_int_15960_to_1596c
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15960 (writeSuccessSuffixInt15960To1596cSpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iPoseProof (write_success_suffix_int_15968_call Q
    with "Hlookup Hint") as "Hcall".
  iPoseProof (instr_pre_to_body 0x15968
    (writeSuccessSuffixInt15968CallSpec Q) with "Hcall") as "HcallPre".
  iPoseProof "Hlookup" as "#Hlookup15960".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15960".
  iPoseProof ("Hlookup15960" $! 0x15960 with "[]") as "#Hinstr15960".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15960.
    done. }
  iApply (instr_pre_intro_Some with "Hinstr15960").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt15960To1596cSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp value tail)
    "(Hsys & H1 & H2 & H10 & H5 & H11 & Hvalue & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hupper & Hreturn & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & %Hshape10)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H1".
  iDestruct "H1" as (r1) "(H1 & %Hshape1)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try iFrame.
Qed.
