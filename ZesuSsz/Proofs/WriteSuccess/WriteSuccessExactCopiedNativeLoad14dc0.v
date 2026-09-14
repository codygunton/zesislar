Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedNativeLoadSpec.
From IslaTraces.write_success_10 Require Import instrs.
Lemma exact_copied_native_load_14dc0_correct `{!islaG Sigma} `{!threadG}
    sp decoded object (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 (drop 16 IslaTraces.write_success_10.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14de0 (exactNativeCopiedLoadState 10 sp decoded object P) -∗
  instr_body 0x14dc0 (exactNativeCopiedLoadState 8 sp decoded object P).
Proof. zesu_block. Qed.
Print Assumptions exact_copied_native_load_14dc0_correct.
