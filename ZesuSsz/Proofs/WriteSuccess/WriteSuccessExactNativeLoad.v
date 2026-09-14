Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactNativeLoadSpec.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactNativeLoad14d80 WriteSuccessExactNativeLoad14da0
  WriteSuccessExactNativeLoad14dc0 WriteSuccessExactNativeLoad14de0
  WriteSuccessNativeCode.
From IslaTraces.write_success_10 Require Import instrs.
From IslaTraces.write_success_11 Require Import instrs.

Lemma exact_native_load_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_10.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_11.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14e00 (exactNativeLoadState sp decoded object P) -∗
  instr_body 0x14d80 (exactNativeLoadState sp decoded object P).
Proof.
  iIntros "H10 H11 Hnext".
  iDestruct (big_sepL_take_drop _ _ 8 with "H10") as "[Hfirst Hrest]".
  iDestruct (big_sepL_take_drop _ _ 8 with "Hrest") as "[Hsecond Hrest]".
  iEval (rewrite drop_drop) in "Hrest".
  iDestruct (big_sepL_take_drop _ _ 8 with "Hrest") as "[Hthird _]".
  iApply (exact_native_load_14d80_correct with "Hfirst").
  iApply (exact_native_load_14da0_correct with "Hsecond").
  iApply (exact_native_load_14dc0_correct with "Hthird").
  iApply (exact_native_load_14de0_correct with "H11 Hnext").
Qed.
Print Assumptions exact_native_load_correct.

Lemma exact_native_load_complete_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x14e00 (exactNativeLoadState sp decoded object P) -∗
  instr_body 0x14d80 (exactNativeLoadState sp decoded object P).
Proof.
  iIntros "#Hcode Hnext".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (instr_lookup_collect _ IslaTraces.write_success_10.instrs.instr_map
    with "Hlookup") as "H10"; first (repeat constructor; reflexivity).
  iPoseProof (instr_lookup_collect _ IslaTraces.write_success_11.instrs.instr_map
    with "Hlookup") as "H11"; first (repeat constructor; reflexivity).
  iApply (exact_native_load_correct with "H10 H11 Hnext").
Qed.
Print Assumptions exact_native_load_complete_correct.
