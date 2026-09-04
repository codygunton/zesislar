Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15168.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15170.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15174.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15178.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1517c.

Lemma write_success_transactions_optional_address_some
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15180 P -∗ instr_body 0x15160 P.
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_optional_address_some_1517c P with
    "Hlookup Hcode Hnext") as "H1517c".
  iPoseProof (write_success_transactions_optional_address_some_15178 P with
    "Hlookup Hcode H1517c") as "H15178".
  iPoseProof (write_success_transactions_optional_address_some_15174 P with
    "Hlookup Hcode H15178") as "H15174".
  iPoseProof (write_success_transactions_optional_address_some_15170 P with
    "Hlookup Hcode H15174") as "H15170".
  iApply (write_success_transactions_optional_address_some_15168 P with
    "Hlookup Hcode H15170").
Qed.
