Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150d8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150dc.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_transactions_chunk_150d8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150dc (writeSuccessTransactionsAt150dcSpec P) -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: iRename select
    (reg_col writeSuccessTransactions150d8OtherRegShapes)%I into "Hother".
  all: iAssert (reg_col writeSuccessTransactions150dcOtherRegShapes)%I
    with "[Hother]" as "HotherFinal"; [iExact "Hother" |].
  all: iRename select (reg_col zesu_ram_sys_regs)%I into "HsysFinal".
  all: iAssert (reg_col zesu_ram_sys_regs)%I with "[HsysFinal]"
    as "HsysBundled";
    [ rewrite /reg_col; iFrame;
      repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done
    | ].
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "HarrayFinal".
  all: iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  all: subst LET0.
  all: subst LET1.
  all: iRename select ((bv_unsigned _) ↦ₘ _)%I into "Hstored150dc".
  all: iRename select ((_ + 4) ↦ₘ? _)%I into "Hscratch150dc".
  all: have Hstore150dcAddress :
    bv_unsigned (sp + BV 64 1656)%bv = bv_unsigned sp + 1656 by bv_solve.
  all: iEval (rewrite Hstore150dcAddress) in
    "Hstored150dc Hscratch150dc".
  all: have Hscratch150dcAddress :
    (bv_unsigned sp + 1656 + 4 = bv_unsigned sp + 1660)%Z by lia.
  all: iEval (rewrite Hscratch150dcAddress) in "Hscratch150dc".
  all: have Hscratch150dcLength :
    (bv_unsigned sp + 1656 + 8 - (bv_unsigned sp + 1660) = 4)%Z by lia.
  all: iEval (rewrite Hscratch150dcLength) in "Hscratch150dc".
  all: iAssert
    (writeSuccessTransactionsMachine150dc
      sp base transactions processed transaction)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal";
    [ rewrite /writeSuccessTransactionsMachine150dc
        /writeSuccessTransactionsScratch150dc;
      iSplitL "HsysBundled"; [iExact "HsysBundled" |];
      iSplitL "HotherFinal"; [iExact "HotherFinal" |];
      iFrame "Hstored150dc Hscratch150dc"; iFrame
    | ].
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: cbn.
  all: iFrame "HmachineFinal HarrayFinal HframeFinal".
  all: rewrite /writeSuccessTransactionsLoadFacts.
  all: repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
