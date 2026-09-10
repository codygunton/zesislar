From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_116 Require Import a15964.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixInt15968Call.

Definition writeSuccessSuffixInt15964HandoffSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    instr_pre 0x15968 (writeSuccessSuffixInt15968CallSpec Q) ∗
    instr_pre 0x1596c (writeSuccessSuffixInt1596cCallPost sp tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15964HandoffSpec) := I.

Lemma write_success_suffix_int_15964_handoff
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr 0x15964 (Some IslaTraces.write_success_116.a15964.a15964) -∗
  instr_body 0x15964 (writeSuccessSuffixInt15964HandoffSpec Q).
Proof.
  iStartProof. iIntros "Hinstr".
  iApply (instr_pre_intro_Some with "Hinstr").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt15964HandoffSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp value tail)
    "(Hsys & H1 & H2 & H10 & H5 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & Hcall & Hreturn & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H1".
  iDestruct "H1" as (r1) "(H1 & %Hshape1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "(H5 & %Hshape5)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hshape11)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try iFrame.
Qed.
