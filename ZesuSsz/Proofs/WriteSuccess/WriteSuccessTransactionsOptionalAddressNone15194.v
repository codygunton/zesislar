From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressNone15198Boundary.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_instr_15194
    `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr 0x15194 (Some IslaTraces.write_success_48.a15194.a15194).
Proof.
  rewrite /InstrSpecs.Lookup.instr_lookup_resources.
  iIntros "#Hlookup".
  iApply ("Hlookup" $! 0x15194).
  iPureIntro.
  rewrite IslaTraces.write_success_blocks.Index.lookup_a15194.
  eauto.
Qed.

Lemma write_success_transactions_optional_address_none_15194
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15198
    (writeSuccessTransactionsOptionalAddressNoneAt15198Spec P) -∗
  instr_body 0x15194
    (writeSuccessTransactionsOptionalAddressNoneAt15194Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_instr_15194 with "Hlookup")
    as "#Hinstr15194".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liAStep.
  Unshelve. all: liAStep.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  rewrite /find_in_context /FindInstrKind /=.
  iExists (IKInstr (Some IslaTraces.write_success_48.a15194.a15194)).
  iSplitL "".
  { iExact "Hinstr15194". }
  cbn.
  li_pm_reduce.
  iIntros "HPC".
  iEval (unfold writeSuccessTransactionsOptionalAddressNoneAt15194Spec)
    in "HPC".
  iDestruct "HPC" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & %Hzero & Hphase)".
  iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessTransactionsMachine1515c) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 & H20 &
      H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  iEval (unfold writeSuccessTransactionPhaseHandoff,
    writeSuccessTransactionsMachine15198).
  iFrame.
  repeat iSplit; try iPureIntro; try done.
  have Hlink : LET0 = BV 64 0x16194 by bv_solve.
  rewrite -Hlink.
  iFrame.
Qed.
