Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_44 Require Import a15154_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15154.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15158.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15154Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions15158Frame.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_15154_to_15158
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15158 (writeSuccessTransactionsAt15158Spec P) -∗
  instr_body 0x15154 (writeSuccessTransactionsAt15154Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve; try lia; try iFrame.
  Unshelve. all: try liARun.
  all: iIntros "HdataOwn".
  all: iIntros "HtransactionTail".
  all: iIntros "HremainingTail".
  all: iDestruct "HtransactionTail" as "(HaccessOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as
    "(HaccessEntriesOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HblobOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HauthOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(%Hvalid & _)".
  all: iDestruct "HremainingTail" as "(Hremaining & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hmmio & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Htrace & HremainingTail)".
  all: iDestruct "HremainingTail" as "(HP & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hinv & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hloop & _)".
  iDestruct (persistent with "Hinv") as "#HinvPersistent".
  iPoseProof "HinvPersistent" as "#HinvCopy".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[HspAlign HinvCopy]".
  iDestruct "HinvCopy" as "[HspLower HinvCopy]".
  iDestruct "HinvCopy" as "[HspUpper _]".
  iDestruct "HspAlign" as "%HspAlign".
  iDestruct "HspLower" as "%HspLower".
  iDestruct "HspUpper" as "%HspUpper".
  have HspAlign8 : bv_unsigned sp `mod` 8 = 0.
  { apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HspAlign; [|lia].
    destruct HspAlign as [factor Hfactor].
    exists (2 * factor). lia. }
  have Hlower120 : ((mapRamBase defaultMap) <= bv_unsigned sp + 120)%Z by lia.
  have Hupper120 : (bv_unsigned sp + 120 < (machineRamEnd defaultMap))%Z by lia.
  all: liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption.
  all: try bv_solve; try lia.
  Unshelve.
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select ((base + 288 * length processed) ↦ₘ∗ suffix)%I into "Hsuffix".
  iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  iAssert (writeSuccessTransactionsMachine15158
    sp base transactions processed transaction)%I with
    "[-Hprefix Hsuffix Hprocessed HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn
       HauthOwn Hremaining Hmmio Htrace HP HinvPersistent Hloop]" as "Hmachine".
  { iEval (unfold writeSuccessTransactionsMachine15158,
      WriteSuccessTransactionsBoundary150e8.writeSuccessTransactionsScratch150e8).
    iFrame. }
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)%I
    with "[HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn]"
    as "HtransactionOwn".
  { iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn).
    iFrame. iPureIntro. split; [exact Hvalid|trivial]. }
  iAssert (writeSuccessTransactions15168Frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed HtransactionOwn Hremaining Hmmio Htrace
      HP HinvPersistent Hloop]"
    as "Hframe".
  { iEval (unfold writeSuccessTransactions15168Frame). iFrame.
    iExact "HinvPersistent". }
  iPoseProof (write_success_transactions_15158_pack P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    with "Hmachine Hframe") as "Hpost".
  iDestruct "Hpost" as
    (sp' base' transaction' transactions' processed' remaining' bytes' prefix'
      suffix' tail') "Hhandoff".
  iExists (tail', suffix', prefix', bytes', remaining', processed', transactions',
    transaction', base', sp', tt)ₗ.
  iExact "Hhandoff".
Qed.
