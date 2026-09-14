Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_116 Require Import a15960.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessSuffixInt15960RawPhaseSpec
    `{!islaG Sigma} `{!threadG} (K : bv 64 -> spec -> iProp Sigma) : iProp Sigma :=
  (∃ (value base : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 64) ↦ₘ value ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base + 64 < (machineRamEnd defaultMap)⌝ ∗
    K base tail ∗
    instr_pre 0x15964
      (reg_col zesu_ram_sys_regs ∗
       "x10" ↦ᵣ RVal_Bits value ∗
       "x2" ↦ᵣ RVal_Bits base ∗
       (bv_unsigned base + 64) ↦ₘ value ∗ K base tail))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15960RawPhaseSpec) := I.

Lemma write_success_suffix_int_15960_raw_phase
    `{!islaG Sigma} `{!threadG} (K : bv 64 -> spec -> iProp Sigma) :
  instr 0x15960 (Some IslaTraces.write_success_116.a15960.a15960) -∗
  instr_body 0x15960 (writeSuccessSuffixInt15960RawPhaseSpec K).
Proof.
  iStartProof. iIntros "Hinstr".
  iApply (instr_pre_intro_Some with "Hinstr").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt15960RawPhaseSpec) in "Hentry".
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
