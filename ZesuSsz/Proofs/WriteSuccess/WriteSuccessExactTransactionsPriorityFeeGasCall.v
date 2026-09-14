Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLimitCall.
From IslaTraces.write_success_41 Require Import instrs.

Lemma transactions_priority_fee_gas_call_correct `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_41.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15138 (transactionGasLimitEntry sp value (BV 64 0x15138)
    (BV 64 0x2401a0b8) (BV 64 16) tail P).
Proof.
  iStartProof. iIntros "#Hjoin #Hgas #Hint #Houtput".
  iPoseProof (transactions_gas_limit_call_correct sp value (BV 64 0x15138)
    (BV 64 0x2401a0b8) (BV 64 16) tail P with "Hgas Hint Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_41.instrs.instr_map /=) in "Hjoin".
  iDestruct "Hjoin" as "#(Hjump & _)". zesu_run.
Qed.
Print Assumptions transactions_priority_fee_gas_call_correct.
