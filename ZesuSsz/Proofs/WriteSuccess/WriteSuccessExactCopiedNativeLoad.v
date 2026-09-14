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

Lemma exact_copied_native_load_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_10.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_11.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14e00 (exactNativeCopiedLoadState 16 sp decoded object P) -∗
  instr_body 0x14d80 (exactNativeLoadState sp decoded object P).
Proof.
  iIntros "H10 H11 Hnext".
  iDestruct (big_sepL_take_drop _ _ 8 with "H10") as "[Hfirst Hrest]".
  iDestruct (big_sepL_take_drop _ _ 8 with "Hrest") as "[Hsecond Hrest]".
  iEval (rewrite drop_drop) in "Hrest".
  iDestruct (big_sepL_take_drop _ _ 8 with "Hrest") as "[Hthird _]".
  iApply (exact_copied_native_load_14d80_correct with "Hfirst").
  iApply (exact_copied_native_load_14da0_correct with "Hsecond").
  iApply (exact_copied_native_load_14dc0_correct with "Hthird").
  iApply (exact_copied_native_load_14de0_correct with "H11 Hnext").
Qed.
Print Assumptions exact_copied_native_load_correct.
