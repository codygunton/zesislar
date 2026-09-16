Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import ZesuSsz.Automation.BlockCodeLookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_72 Require Import instrs.
From IslaTraces.write_success_73 Require Import instrs.

Lemma code_lookup_two_blocks `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  ([∗ list] block ∈ [IslaTraces.write_success_72.instrs.instr_map;
    IslaTraces.write_success_73.instrs.instr_map],
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
Proof.
  iStartProof. iIntros "#Hcode".
  iApply (instr_lookup_collect_blocks with "Hcode").
  repeat constructor; reflexivity.
Qed.
Print Assumptions code_lookup_two_blocks.
