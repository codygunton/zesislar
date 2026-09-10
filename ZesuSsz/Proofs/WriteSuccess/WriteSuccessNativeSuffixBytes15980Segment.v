Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixBytes1598cCall.

Definition writeSuccessSuffixBytes15980To15990Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits data ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 8) ↦ₘ size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 8 < 0x40000000⌝ ∗
    instr_pre 0x15990
      (writeSuccessSuffixBytes15990CallPost
        sp data size data oldS1 bytes tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixBytes15980To15990Spec) := I.

Lemma write_success_suffix_bytes_15980_to_15990
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15980 (writeSuccessSuffixBytes15980To15990Spec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hbytes".
  iPoseProof (write_success_suffix_bytes_1598c_call Q
    with "Hlookup Hbytes") as "Hcall".
  iPoseProof (instr_pre_to_body 0x1598c
    (writeSuccessSuffixBytes1598cCallSpec Q) with "Hcall") as "HcallPre".
  iPoseProof "Hlookup" as "#Hlookup15980".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15980".
  iPoseProof ("Hlookup15980" $! 0x15980 with "[]") as "#Hinstr15980".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15980.
    done. }
  iApply (instr_pre_intro_Some with "Hinstr15980").
  iIntros "Hentry HPC".
  iEval (rewrite /writeSuccessSuffixBytes15980To15990Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp data size oldS1 bytes tail)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hsize &
      Hstack & Hdata & %Hlen & Hmmio & Htrace & %Halign & %Hmin &
      %Hmax & %Hupper & Hreturn & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H1".
  iDestruct "H1" as (r1) "(H1 & %Hshape1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & %Hshape10)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hshape11)".
  have Hdata0 : (data + BV 64 0)%bv = data by bv_solve.
  have HsizeExt : bv_sign_extend 64 size = size by
    apply bv_sign_extend_64_idemp.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try iFrame.
  all: try rewrite Hdata0 HsizeExt.
  all: try bv_solve.
  all: try reflexivity.
  all: lazymatch goal with |- ?G => fail "15980 segment residual" G end.
Qed.
