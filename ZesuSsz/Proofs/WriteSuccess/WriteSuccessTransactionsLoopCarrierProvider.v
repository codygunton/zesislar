From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierCompose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierEntry.

Lemma write_success_transactions_loop_carrier_prefix_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  □ instr_pre 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P).
Proof.
  iIntros "#Hbody".
  iModIntro.
  iApply instr_pre_to_body.
  iNext.
  iExact "Hbody".
Qed.

Lemma write_success_transactions_loop_carrier_body_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P) -∗
  instr_body 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P).
Proof.
  iIntros "Hprefix #Hlookup #Hloop".
  iApply (write_success_transactions_loop_carrier_compose P
    with "Hprefix Hlookup Hloop").
Qed.

Lemma write_success_transactions_loop_carrier_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P) -∗
  instr_body 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P).
Proof.
  iIntros "#HprefixBody #Hlookup #Hloop".
  iPoseProof "HprefixBody" as "HprefixBody'".
  iApply (write_success_transactions_loop_carrier_body_provider P
    with "HprefixBody' Hlookup Hloop").
Qed.
