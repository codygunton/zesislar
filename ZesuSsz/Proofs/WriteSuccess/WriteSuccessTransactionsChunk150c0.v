Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150c0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150c4.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_transactions_chunk_150c0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150c4 (writeSuccessTransactionsAt150c4Spec P) -∗
  instr_body 0x150c0 (writeSuccessTransactionsAt150c0Spec P).
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
    (reg_col writeSuccessTransactions150c0OtherRegShapes)%I into "Hother".
  all: iAssert (reg_col writeSuccessTransactions150c4OtherRegShapes)%I
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
  all: iRename select
    ((bv_unsigned sp + 168 + 8) ↦ₘ? 8)%I into "Hscratch150c4".
  all: have Hscratch150c4Address :
    (bv_unsigned sp + 168 + 8 = bv_unsigned sp + 176)%Z by lia.
  all: iEval (rewrite Hscratch150c4Address) in "Hscratch150c4".
  all: iAssert
    (writeSuccessTransactionsMachine150c4
      sp base transactions processed transaction)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal";
    [ rewrite /writeSuccessTransactionsMachine150c4
        /writeSuccessTransactionsScratch150c4;
      iSplitL "HsysBundled"; [iExact "HsysBundled" |];
      iSplitL "HotherFinal"; [iExact "HotherFinal" |];
      iFrame
    | ].
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: cbn.
  all: iFrame "HmachineFinal HarrayFinal HframeFinal".
  all: rewrite /writeSuccessTransactionsLoadFacts.
  all: repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
