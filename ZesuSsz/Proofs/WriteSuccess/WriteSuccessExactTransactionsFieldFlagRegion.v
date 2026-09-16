Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFieldFlagEntry WriteSuccessExactTransactionsFieldLoads
  WriteSuccessExactTransactionsFlagLoads.

Lemma transactions_field_flag_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f68 (transactionFlagLoadPost row base bytes index
    (transactionFieldFlagRetained sp bytes index P)) -∗
  instr_body 0x14f44 (transactionFieldLoadEntry sp row base bytes index
    (transactionFieldFlagCaller bytes index P)).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof (transactions_flag_loads_correct row base bytes index
    (transactionFieldFlagRetained sp bytes index P) with "Hcode Hnext") as "Hflags".
  iApply (transactions_field_loads_correct sp row base bytes index
    (transactionFieldFlagCaller bytes index P) with "Hcode").
  iApply (instr_pre_wand 0x14f5c 0x14f5c false false with "Hflags"); [done | done |].
  iApply transactions_field_flag_entry.
Qed.
Print Assumptions transactions_field_flag_region_correct.
