Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BlockCodeLookup.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsPublic.
Import ListNotations.

Lemma draft_withdrawal_code_group_b `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  ([∗ list] block ∈
    [IslaTraces.write_success_93.instrs.instr_map;
     IslaTraces.write_success_94.instrs.instr_map;
     IslaTraces.write_success_95.instrs.instr_map],
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
Proof.
  have Hblocks : Forall (fun block => Forall (fun instruction =>
      IslaTraces.write_success_blocks.Index.lookup instruction.1 =
        Some instruction.2) block)
    [IslaTraces.write_success_93.instrs.instr_map;
     IslaTraces.write_success_94.instrs.instr_map;
     IslaTraces.write_success_95.instrs.instr_map].
  { repeat constructor; reflexivity. }
  iIntros "#Hlookup".
  iApply (instr_lookup_collect_blocks _ _ Hblocks with "Hlookup").
Qed.

Print Assumptions draft_withdrawal_code_group_b.
