Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_81 Require Import instrs.
Local Remove Hints IslaTraces.write_success_81.a155fc_spec.a155fc_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15600_spec.a15600_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15604_spec.a15604_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15608_spec.a15608_spec_inst : typeclass_instances.

Lemma authorization_third_words_correct `{!islaG Sigma} `{!threadG} sp bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_81.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1560c (authorizationWordsAtPost sp bytes 64 P) -∗
  instr_body 0x155fc (authorizationWordsEntry sp bytes P).
Proof. move => *. zesu_block. Qed.
Print Assumptions authorization_third_words_correct.
