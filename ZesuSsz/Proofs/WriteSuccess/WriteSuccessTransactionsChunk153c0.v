Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary153c0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary153d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_153c0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x153d0 (writeSuccessTransactionsAt153d0Spec P) -∗
  instr_body 0x153c0 (writeSuccessTransactionsAt153c0Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
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
  Unshelve. all: repeat iIntros "?".
  all: repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  all: liARun.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  all: liARun.
  all: iFrame.
  all: iDestruct select ((bv_unsigned sp - 48) ↦ₘ? 32)%I as "Hstack0".
  all: iDestruct select ((bv_unsigned sp - 16 + 16) ↦ₘ? 104)%I as "Hstack2".
  all: iSplit.
  all: try (replace 86992%bv with (Z_to_bv 64 (86988 + 4)) by bv_solve;
    iExact "H1").
  all: iApply (mem_mapsto_uninit_combine 32 with
    "[Hstack0] [Hstack Hstack2]"); [lia|iExact "Hstack0"|].
  all: iApply (mem_mapsto_uninit_combine 16 with
    "[Hstack] [Hstack2]"); [lia|iExact "Hstack"|iExact "Hstack2"].
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try bv_solve.
  all: try lia.
Qed.
