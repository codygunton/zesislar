Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactNativeLoadSpec.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedNativeLoadSpec.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactCopiedNativeLoad14d80 WriteSuccessExactCopiedNativeLoad14da0
  WriteSuccessExactCopiedNativeLoad14dc0 WriteSuccessExactCopiedNativeLoad14de0
  WriteSuccessNativeCode.
From IslaTraces.write_success_10 Require Import instrs.
From IslaTraces.write_success_11 Require Import instrs.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedNativeLoad.
Lemma exact_copied_native_load_complete_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x14e00 (exactNativeCopiedLoadState 16 sp decoded object P) -∗
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
  iApply (exact_copied_native_load_correct with "H10 H11 Hnext").
Qed.
Print Assumptions exact_copied_native_load_complete_correct.
