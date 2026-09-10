From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixInt159acCall.

Definition writeSuccessSuffixInt159a0To159b0Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp saved value : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 96) ↦ₘ saved ∗
    (bv_unsigned sp + 80) ↦ₘ value ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 96 < 0x40000000⌝ ∗
    instr_pre 0x159b0 (writeSuccessSuffixInt159b0CallPost sp tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixInt159a0To159b0Spec) := I.

Lemma write_success_suffix_int_159a0_to_159b0
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x159a0 (writeSuccessSuffixInt159a0To159b0Spec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iPoseProof (write_success_suffix_int_159ac_call Q
    with "Hlookup Hint") as "Hcall".
  iPoseProof (instr_pre_to_body 0x159ac
    (writeSuccessSuffixInt159acCallSpec Q) with "Hcall") as "HcallPre".
  iPoseProof "Hlookup" as "#Hlookup159a0".
  iEval (rewrite /instr_lookup_resources) in "Hlookup159a0".
  iPoseProof ("Hlookup159a0" $! 0x159a0 with "[]") as "#Hinstr159a0".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a159a0.
    done. }
  iApply (instr_pre_intro_Some with "Hinstr159a0").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixInt159a0To159b0Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp saved value tail)
    "(Hsys & H1 & H2 & H5 & H8 & H10 & H11 & Hsaved & Hvalue &
      Hstack & Hmmio & Htrace & %Halign & %Hmin & %Hmax & %Hupper &
      Hreturn & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H1".
  iDestruct "H1" as (r1) "(H1 & %Hshape1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H8".
  iDestruct "H8" as (r8) "(H8 & %Hshape8)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & %Hshape10)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try iFrame.
Qed.
