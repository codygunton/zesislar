From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fe0Loads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_transactions_chunk_14ff0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15018 (writeSuccessTransactionsAt15018Spec P) -∗
  instr_body 0x14ff0 (writeSuccessTransactionsAt14ff0Spec P).
Proof.
  move => *.
  iStartProof.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: have Hx7Post : LET16 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 268))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 267))
          (BV 64 16)) by bv_solve.
  all: have Hx12Post : LET14 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 266))
          (BV 64 8))
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265)) by bv_solve.
  all: have Hx13Post : LET12 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 280))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 279))
          (BV 64 16)) by bv_solve.
  all: have Hx19Post : LET4 =
      bv_shiftl
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 266))
        (BV 64 8) by bv_solve.
  all: have Hx28Post : LET18 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 270))
          (BV 64 8))
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 269)) by bv_solve.
  all: iRename select ("x7" ↦ᵣ RVal_Bits LET16)%I into "Hx7Post".
  all: iRename select ("x12" ↦ᵣ RVal_Bits LET14)%I into "Hx12Post".
  all: iRename select ("x13" ↦ᵣ RVal_Bits LET12)%I into "Hx13Post".
  all: iRename select ("x19" ↦ᵣ RVal_Bits LET4)%I into "Hx19Post".
  all: iRename select ("x28" ↦ᵣ RVal_Bits LET18)%I into "Hx28Post".
  all: iEval (rewrite Hx7Post) in "Hx7Post".
  all: iEval (rewrite Hx12Post) in "Hx12Post".
  all: iEval (rewrite Hx13Post) in "Hx13Post".
  all: iEval (rewrite Hx19Post) in "Hx19Post".
  all: iEval (rewrite Hx28Post) in "Hx28Post".
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "Harray".
  all: iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "Hphase".
  all: iExists (tail, suffix, prefix, bytes, remaining, transactions,
    transaction, sp, tt)ₗ.
  all: iSplitR "Harray Hphase".
  {
    iIntros "(HsysFinal & Hx10Final & Hx18Final & Hx20Final & Hx29Final &
      Hx27Final)".
    rewrite /writeSuccessTransactionsMachine15028
      /writeSuccessTransactionsScratch14fc8.
    iFrame;
    try prepare_sidecond;
    try bv_solve;
    try iFrame.
  }
  {
    iFrame.
    rewrite /writeSuccessTransactionsLoadFacts;
    repeat iSplit; try iPureIntro; try assumption; done.
  }
Qed.
