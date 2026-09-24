Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsPublic.
From ZesuSsz.Proofs.WriteSuccess Require Import
  ContractChainWithdrawalCodeA ContractChainWithdrawalCodeB
  ContractChainWithdrawalCodeC.
Import ListNotations.

Lemma draft_withdrawal_loop_code_from_lookup `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  withdrawalLoopCode.
Proof.
  iIntros "#Hlookup".
  rewrite /withdrawalLoopCode.
  change ([∗ list] block ∈
    [IslaTraces.write_success_90.instrs.instr_map;
     IslaTraces.write_success_91.instrs.instr_map;
     IslaTraces.write_success_92.instrs.instr_map] ++
    [IslaTraces.write_success_93.instrs.instr_map;
     IslaTraces.write_success_94.instrs.instr_map;
     IslaTraces.write_success_95.instrs.instr_map] ++
    [IslaTraces.write_success_02.instrs.instr_map;
     IslaTraces.write_success_07.instrs.instr_map;
     IslaTraces.write_success_01.instrs.instr_map],
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
  rewrite !big_sepL_app.
  iSplit.
  - iApply (draft_withdrawal_code_group_a with "Hlookup").
  - iSplit.
    + iApply (draft_withdrawal_code_group_b with "Hlookup").
    + iApply (draft_withdrawal_code_group_c with "Hlookup").
Qed.

Print Assumptions draft_withdrawal_loop_code_from_lookup.
