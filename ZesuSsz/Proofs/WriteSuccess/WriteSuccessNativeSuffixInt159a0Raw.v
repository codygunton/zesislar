From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_122 Require Import a159a0 a159a4.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessSuffixInt159a0RawPhaseSpec
    `{!islaG Sigma} `{!threadG}
    (K : bv 64 -> bv 64 -> iProp Sigma) : iProp Sigma :=
  (∃ (saved base : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 96) ↦ₘ saved ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base + 96 < 0x40000000⌝ ∗
    K base saved ∗
    instr_pre 0x159a4
      (reg_col zesu_ram_sys_regs ∗
       "x8" ↦ᵣ RVal_Bits saved ∗
       "x2" ↦ᵣ RVal_Bits base ∗
       (bv_unsigned base + 96) ↦ₘ saved ∗ K base saved))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159a0RawPhaseSpec) := I.

Lemma write_success_suffix_int_159a0_raw_phase
    `{!islaG Sigma} `{!threadG}
    (K : bv 64 -> bv 64 -> iProp Sigma) :
  instr 0x159a0 (Some IslaTraces.write_success_122.a159a0.a159a0) -∗
  instr_body 0x159a0 (writeSuccessSuffixInt159a0RawPhaseSpec K).
Proof.
  iStartProof. iIntros "Hinstr".
  iApply (instr_pre_intro_Some with "Hinstr").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt159a0RawPhaseSpec) in "Hentry".
  iDestruct "Hentry" as (saved base)
    "(Hsys & H8 & H2 & Hsaved & %Halign & %Hrange & HK & Hnext)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H8".
  iDestruct "H8" as (r8) "(H8 & %Hshape8)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: try iFrame.
Qed.

Definition writeSuccessSuffixInt159a4RawPhaseSpec
    `{!islaG Sigma} `{!threadG}
    (K : bv 64 -> bv 64 -> iProp Sigma) : iProp Sigma :=
  (∃ (value base : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 80) ↦ₘ value ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base + 80 < 0x40000000⌝ ∗
    K base value ∗
    instr_pre 0x159a8
      (reg_col zesu_ram_sys_regs ∗
       "x10" ↦ᵣ RVal_Bits value ∗
       "x2" ↦ᵣ RVal_Bits base ∗
       (bv_unsigned base + 80) ↦ₘ value ∗ K base value))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159a4RawPhaseSpec) := I.

Lemma write_success_suffix_int_159a4_raw_phase
    `{!islaG Sigma} `{!threadG}
    (K : bv 64 -> bv 64 -> iProp Sigma) :
  instr 0x159a4 (Some IslaTraces.write_success_122.a159a4.a159a4) -∗
  instr_body 0x159a4 (writeSuccessSuffixInt159a4RawPhaseSpec K).
Proof.
  iStartProof. iIntros "Hinstr".
  iApply (instr_pre_intro_Some with "Hinstr").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt159a4RawPhaseSpec) in "Hentry".
  iDestruct "Hentry" as (value base)
    "(Hsys & H10 & H2 & Hvalue & %Halign & %Hrange & HK & Hnext)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & %Hshape10)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
  Unshelve. all: try iFrame.
Qed.
