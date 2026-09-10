Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_transactions_chunk_150dc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150e0 (writeSuccessTransactionsAt150e0Spec P) -∗
  instr_body 0x150dc (writeSuccessTransactionsAt150dcSpec P).
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
    (reg_col writeSuccessTransactions150dcOtherRegShapes)%I into "Hother".
  all: iAssert (reg_col writeSuccessTransactions150e0OtherRegShapes)%I
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
  all: iRename select ((bv_unsigned _) ↦ₘ _)%I into "Hstored150e0".
  all: iRename select
    ((bv_unsigned sp + 1680) ↦ₘ? _)%I into "Hprefix150e0".
  all: iRename select ((_ + 1) ↦ₘ? _)%I into "Hsuffix150e0".
  all: have Hstore150e0Address :
    bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744 by bv_solve.
  all: iEval (rewrite Hstore150e0Address) in
    "Hstored150e0 Hprefix150e0 Hsuffix150e0".
  all: have Hstore150e0Value :
    bv_extract 0 8
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 264)) =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 264 by bv_solve.
  all: iEval (rewrite Hstore150e0Value) in "Hstored150e0".
  all: have Hprefix150e0Length :
    (bv_unsigned sp + 1744 - (bv_unsigned sp + 1680) = 64)%Z by lia.
  all: iEval (rewrite Hprefix150e0Length) in "Hprefix150e0".
  all: have Hsuffix150e0Address :
    (bv_unsigned sp + 1744 + 1 = bv_unsigned sp + 1745)%Z by lia.
  all: iEval (rewrite Hsuffix150e0Address) in "Hsuffix150e0".
  all: have Hsuffix150e0Length :
    (bv_unsigned sp + 1680 + 216 - (bv_unsigned sp + 1745) = 151)%Z
      by lia.
  all: iEval (rewrite Hsuffix150e0Length) in "Hsuffix150e0".
  all: iAssert
    (writeSuccessTransactionsMachine150e0
      sp base transactions processed transaction)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal";
    [ rewrite /writeSuccessTransactionsMachine150e0
        /writeSuccessTransactionsScratch150e0;
      iSplitL "HsysBundled"; [iExact "HsysBundled" |];
      iSplitL "HotherFinal"; [iExact "HotherFinal" |];
      iFrame "Hstored150e0 Hprefix150e0 Hsuffix150e0"; iFrame
    | ].
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: cbn.
  all: iFrame "HmachineFinal HarrayFinal HframeFinal".
  all: rewrite /writeSuccessTransactionsLoadFacts.
  all: repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
