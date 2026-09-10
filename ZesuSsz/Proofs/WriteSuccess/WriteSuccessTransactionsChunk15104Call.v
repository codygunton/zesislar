From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15104.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15108.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15104_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15108 (writeSuccessTransactionsAt15108Spec P) -∗
  instr_body 0x15104 (writeSuccessTransactionsAt15104Spec P).
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
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  all: iDestruct select (_ ∗ _)%I as
    "(Hremaining & Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  all: iPoseProof "Hinvariant" as "#HinvariantCopy".
  all: iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: iExists
    (writeSuccessTransactionPhaseEvents TransactionGasPrice sp transaction
      (writeSuccessTransactionsEvents sp remaining tail), tt)ₗ.
  all: iFrame "Hmmio Htrace".
  all: repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  all: iApply (instr_pre_wand 0x15108 0x15108 false true with "Hnext");
    [done | done |].
  all: iIntros "Hpost".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  all: iDestruct select ((bv_unsigned sp - 48) ↦ₘ? 32)%I as "Hlower".
  all: iDestruct select ((bv_unsigned sp - 16 + 16) ↦ₘ? 104)%I
    as "Hupper".
  all: have HupperAddress : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  all: iEval (rewrite HupperAddress) in "Hupper".
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower Hstack]" as "Hlower48".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    have -> : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
    iExact "Hstack". }
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hupper]" as "HscratchPrefix".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
    iExact "Hupper". }
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x15108))%I
    with "[H1]" as "H1target".
  { replace (BV 64 0x15108) with (Z_to_bv 64 (0x15104 + 4)) by bv_solve.
    iExact "H1". }
  all: iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  all: iFrame "Hsys H1target H2 H5 H10 H11 HscratchPrefix Hmmio Htrace
    Hremaining HP Hinvariant Hexit".
  all: iFrame.
  all: repeat iSplit; iPureIntro; try assumption; try bv_solve; lia.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
Qed.
