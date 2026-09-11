Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryBody.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryExit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_loop_carrier_compose
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P) -∗
  instr_body 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P).
Proof.
  iIntros "Hbody #Hlookup #Hloop".
  liARun.
  - iApply (write_success_transactions_loop_carrier_entry_exit
      P sp base processed remaining tail first second third fourth items H5 H13).
    rewrite /writeSuccessTransactionsLoopCarrierExitBranchFrame.
    iFrame. iSplit; first (iPureIntro; exact H0). iAssumption.
  - have Hfacts : writeSuccessTransactionsLoopEntryFacts
        sp base processed remaining.
    { rewrite /writeSuccessTransactionsLoopEntryFacts.
      repeat split; assumption. }
    iPoseProof (write_success_transactions_loop_carrier_entry_body
      P sp base processed remaining tail first second third fourth items
      Hfacts H13 with "[-]") as "Hentry".
    { rewrite /writeSuccessTransactionsLoopCarrierFrame.
      iFrame. iSplit; first (iPureIntro; exact H0).
      iSplit; first iAssumption.
      rewrite /writeSuccessTransactionsInvariant.
      repeat iSplit; try (iPureIntro; reflexivity);
        try (iPureIntro; assumption). }
    iEval (unfold writeSuccessTransactionsAt14f08CarrierSpec) in "Hentry".
    iDestruct "Hentry" as
      (sp' base' transaction transactions processed' remaining' bytes prefix
        suffix tail' first' second' third' fourth' items') "Hentry".
    iExists
      (items', fourth', third', second', first', tail', suffix, prefix, bytes,
        remaining', processed', transactions, transaction, base', sp', tt)ₗ.
    iExact "Hentry".
Unshelve.
all: prepare_sidecond.
all: try (f_equal; exact H13).
all: try (rewrite (write_success_transactions_loop_exit_remaining_nil
  processed remaining H5 H13); rewrite app_nil_r; reflexivity).
all: try (apply bv_eq; rewrite bv_and_unsigned !bv_unsigned_BV; exact H12).
Qed.
