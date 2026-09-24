Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_126 Require Import instrs.
Import ListNotations.

Lemma draft_epilogue_code_from_lookup `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_126.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I.
Proof.
  have Hblock : Forall (fun instruction =>
      IslaTraces.write_success_blocks.Index.lookup instruction.1 =
        Some instruction.2)
    IslaTraces.write_success_126.instrs.instr_map.
  { repeat constructor; reflexivity. }
  iIntros "#Hlookup".
  iApply (instr_lookup_collect _ _ Hblock with "Hlookup").
Qed.

Print Assumptions draft_epilogue_code_from_lookup.
