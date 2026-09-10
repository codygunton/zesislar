Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixInt159a0Segment.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixScalarSetups.

Definition writeSuccessSuffixJump15990To159b0Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   writeSuccessSuffixInt159a0To159b0Spec Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixJump15990To159b0Spec) := I.

Lemma write_success_suffix_jump_15990_to_159b0
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15990 (writeSuccessSuffixJump15990To159b0Spec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iPoseProof (write_success_suffix_int_159a0_to_159b0 Q
    with "Hlookup Hint") as "HnextBody".
  iPoseProof (instr_pre_to_body 0x159a0
    (writeSuccessSuffixInt159a0To159b0Spec Q) with "HnextBody")
    as "Hnext".
  iPoseProof (write_success_suffix_jump_15990
    (writeSuccessSuffixInt159a0To159b0Spec Q) with "Hlookup") as "Hjump".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iApply "Hjump".
  rewrite /writeSuccessSuffixJump15990To159b0Spec
    /writeSuccessSuffixJump15990Spec.
  iDestruct "Hentry" as "(Hsys & Hsegment)".
  iFrame "Hsys Hsegment".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iExact "Hnext".
  all: lazymatch goal with |- ?G => fail "15990 jump residual" G end.
Qed.
