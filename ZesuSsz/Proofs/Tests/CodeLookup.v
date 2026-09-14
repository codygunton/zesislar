Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_41 Require Import instrs.
From IslaTraces.write_success_blocks Require Import Index.

Lemma test_code_lookup_block_frame `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  (instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup ∗ P ∗ True)%I -∗
  (([∗ list] instruction ∈ IslaTraces.write_success_41.instrs.instr_map,
     instr instruction.1 (Some instruction.2)) ∗ P ∗ True)%I.
Proof.
  iIntros "(#Hcode & HP & _)". iFrame "HP".
  iApply instr_lookup_collect; last iExact "Hcode".
  repeat constructor; reflexivity.
Qed.
Print Assumptions test_code_lookup_block_frame.
