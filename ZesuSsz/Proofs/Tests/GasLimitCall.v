Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLimitCall.
From IslaTraces.write_success_43 Require Import instrs.

Lemma gas_limit_call_uses_closed_encoder_int
    `{!islaG Sigma} `{!threadG}
    sp value oldra old5 old11 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntExactCallSpec -∗
  instr_body 0x15148
    (transactionGasLimitEntry sp value oldra old5 old11 tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions gas_limit_call_uses_closed_encoder_int.
