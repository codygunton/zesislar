Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64None.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Lemma optional_u64_none_exact_call_correct `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (optionalU64NoneExactCallEntry pointer sp ret old_x5 old_x6
    old_x11 bytes tail P).
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Houtput".
  iDestruct (big_sepL_take_drop _ _ 2 with "Hoptional") as "[#Hbranch _]".
  iDestruct (big_sepL_take_drop _ _ 15 with "Hoptional") as "[_ #Htail]".
  iApply optional_u64_none_exact_call_entry.
  iApply (optional_u64_none_exact_correct with "Hbranch Htail Hboolean Houtput").
Qed.

Print Assumptions optional_u64_none_exact_call_correct.
