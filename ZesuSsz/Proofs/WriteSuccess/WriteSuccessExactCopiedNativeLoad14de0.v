Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedNativeLoadSpec.
From IslaTraces.write_success_11 Require Import instrs.
Lemma exact_copied_native_load_14de0_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_11.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14e00 (exactNativeCopiedLoadState 16 sp decoded object P) -∗
  instr_body 0x14de0 (exactNativeCopiedLoadState 10 sp decoded object P).
Proof. zesu_block. Qed.
Print Assumptions exact_copied_native_load_14de0_correct.
