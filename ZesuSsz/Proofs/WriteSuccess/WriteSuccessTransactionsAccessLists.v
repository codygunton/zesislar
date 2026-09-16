Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsLoopProof.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary153c0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessListsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessEntryFrame.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_access_lists
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x153c0 (writeSuccessTransactionsAt153c0Spec P) -∗
  instr_body 0x151d0 (writeSuccessTransactionsAt151d0Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hmemcpy #Houtput #Hint Hnext".
  iAssert (□ ∀ (x19 : bv 64) (Q : iProp Sigma),
      instr_pre 0x151d4 (writeSuccessAccessListsLoopSpec x19 Q))%I
    with "[]" as "#HaccessLoop".
  { iModIntro. iIntros (x19 Q).
    iApply (write_success_access_lists_loop_pre x19 Q with
      "Hlookup Hcode Hmemcpy Houtput Hint"). }
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iIntros "Hto _ _ Hstate HPC".
  set (Paccess := writeSuccessTransactionsAccessFrame sp
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction)
    (writeSuccessAccessEntriesBytes
      (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
        transaction))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
      WriteSuccessTransactionsSpec.TransactionBlobCount sp transaction
      (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
        sp remaining tail))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)
    P).
  iPoseProof ("HaccessLoop" $!
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
    Paccess) as
    "#HaccessLoopConcrete".
  liARun.
  iRename select
    ("x22" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200))%I
    into "Hx22".
  iRename select
    ("x27" ↦ᵣ RVal_Bits
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)))%I
    into "Hx27".
  iAssert (writeSuccessTransactionsScratch1519c
      sp base transactions processed transaction)%I
    with "[-Hstate Hx22 Hx27 Hnext]" as "Hscratch".
  { rewrite /writeSuccessTransactionsScratch1519c.
    iFrame. }
  iDestruct "Hstate" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & Hmmio &
      Htrace & HP & Hinvariant & Hexit & _)".
  iPoseProof (write_success_transactions_access_entry_frame
    sp base transaction transactions processed remaining bytes prefix suffix
    with "Htransaction Hinvariant") as "HentryFrame".
  iEval (rewrite /writeSuccessTransactionsAccessEntryResources)
    in "HentryFrame".
  iDestruct "HentryFrame" as
    "(Hempty & HaccessBytes & Hentries & HtransactionRestore &
      HaccessInvariant & Hinvariant & %HbaseWord & %HcountWord &
      %HaccessBytesEq)".
  iPoseProof (write_success_transactions_access_scratch_split
    sp base transactions processed transaction
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
    (length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction))
    HbaseWord HcountWord with "Hscratch")
    as "(HaccessScratch & HscratchRestore)".
  iAssert Paccess with
    "[HscratchRestore HtransactionRestore Hprefix Hsuffix Hprocessed Hremaining
      HP Hinvariant Hexit]" as "HPaccess".
  { rewrite /Paccess /writeSuccessTransactionsAccessFrame.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iFrame "HscratchRestore HtransactionRestore Hprefix Hsuffix Hprocessed
      Hremaining HP Hinvariant Hexit".
    iSplit; [done|]. iSplit; [done|].
    iSplit; [iPureIntro; symmetry; exact HaccessBytesEq|].
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. done. }
  iAssert Paccess with "[HPaccess]" as "HPaccessFolded".
  { iExact "HPaccess". }
  iPoseProof (write_success_transactions_access_exit sp
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction)
    (writeSuccessAccessEntriesBytes
      (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
      WriteSuccessTransactionsSpec.TransactionBlobCount sp transaction
      (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
        sp remaining tail))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)
    P with "Hnext") as "HexitAccess".
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
       WriteSuccessTransactionsSpec.TransactionBlobCount sp transaction
       (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail),
     bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32),
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200,
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232,
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176,
     writeSuccessAccessEntriesBytes
       (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
          transaction),
     [],
     writeSuccessAccessEntriesBytes
       (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
          transaction),
     WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction,
     [],
     WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction,
     bv_unsigned
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208),
     tt)ₗ.
  iSplit; [iPureIntro; bv_solve|].
  iSplitL "Hx22"; [iExact "Hx22"|].
  iSplitL "Hx27"; [iExact "Hx27"|].
  iSplitL "Hempty"; [iExact "Hempty"|].
  rewrite Z.mul_0_r Z.add_0_r.
  iSplitL "HaccessBytes"; [iExact "HaccessBytes"|].
  iSplit; [done|].
  iSplitL "Hentries"; [iExact "Hentries"|].
  iSplitL "HaccessScratch"; [iExact "HaccessScratch"|].
  iSplitL "Hmmio"; [iExact "Hmmio"|].
  iSplitL "Htrace"; [iExact "Htrace"|].
  iSplitL "HPaccessFolded"; [iExact "HPaccessFolded"|].
  iSplitL "HaccessInvariant"; [iExact "HaccessInvariant"|].
  iSplitL "HexitAccess"; [iExact "HexitAccess"|].
  done.
  Unshelve. all: prepare_sidecond; bv_solve.
Qed.
