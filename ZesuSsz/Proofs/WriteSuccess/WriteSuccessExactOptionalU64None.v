Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneTail.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Lemma optional_u64_none_exact_correct `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ drop 15 IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (optionalU64NoneExactEntry pointer sp ret old_x5 old_x6
    old_x11 bytes tail P).
Proof.
  iStartProof. iIntros "#Hentry #Htail #Hboolean #Houtput".
  iApply (optional_u64_none_exact_entry with "Hentry").
  iApply (optional_u64_none_exact_tail with "Htail").
  iApply (encoder_boolean_exact_framed_correct with "Hboolean Houtput").
Qed.

Print Assumptions optional_u64_none_exact_correct.
