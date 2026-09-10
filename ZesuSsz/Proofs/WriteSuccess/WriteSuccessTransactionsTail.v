From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1565c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsTailCompose.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Import ListNotations.

Lemma write_success_transactions_tail
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  instr_body 0x1565c (writeSuccessTransactionsAt1565cSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hloop".
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
  Unshelve. all: iIntros "Hdata Htransaction Houter"; liARun.
  Unshelve.
  all: try lazymatch goal with
    | |- SHELVED_SIDECOND _ => prepare_sidecond
    end.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: li_unfold_lets_in_context.
  all: simpl; try liToSyntaxGoal.
  all: unLET.
  all: iDestruct "Htransaction" as
    "(Haccess & Hentries & Hblob & Hauthorization & %HtransactionValid & _)".
  all: iDestruct "Houter" as
    "(HremainingOwn & Hmmio & Htrace & HP & Hinv & Hexit & _)".
  all: (iAssert (writeSuccessTransactionOwn transaction)%I
    with "[Hdata Haccess Hentries Hblob Hauthorization]" as "HtransactionOwn";
    [rewrite /writeSuccessTransactionOwn; iFrame; done |]).
  all: iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn
      processed)%I into "HprocessedOwn".
  all: iRename select (base ↦ₘ∗ prefix)%I into "HbasePrefix".
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix)%I
    into "HbaseSuffix".
  all: (iAssert (writeSuccessTransactionsScratch15620
      sp base transactions processed transaction)%I
    with "[- HbasePrefix HbaseSuffix HprocessedOwn HremainingOwn Hmmio Htrace
      HP Hinv Hexit HtransactionOwn]" as "Hscratch15620";
    [rewrite /writeSuccessTransactionsScratch15620
       /writeSuccessTransactionsScratch15620Tail;
     iFrame; repeat iSplit; try done |]).
  all: iApply (write_success_transactions_tail_compose P
    (Z_to_bv 64 (Z.of_nat (length processed)) + BV 64 1)%bv sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "[] Hscratch15620 HbasePrefix HbaseSuffix HprocessedOwn
      HtransactionOwn HremainingOwn Hmmio Htrace HP Hinv Hexit").
  all: iPureIntro; rewrite length_app; cbn; bv_solve.
  Unshelve.
  all: try exact inhabitant.
  all: try lazymatch goal with
    | |- SHELVED_SIDECOND _ => prepare_sidecond
    end.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
