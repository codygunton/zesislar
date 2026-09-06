From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150d8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150ec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactionsAt150d8CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine150d8Carrier
      sp base transactions processed transaction
      first second third fourth items ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150d8CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_150d8_to_150ec_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (HtransactionLength : length (writeSuccessTransactionBytes transaction) = 288%nat)
    (HbaseAlign : (base + 288 * Z.of_nat (length processed)) `mod` 8 = 0)
    (HbaseLower : 0x20000000 <= base + 288 * Z.of_nat (length processed))
    (HbaseUpper : base + 288 * Z.of_nat (length processed) + 288 < 0x40000000)
    (HspAlign8 : bv_unsigned sp `mod` 8 = 0)
    (HspLower48 : 0x20000000 <= bv_unsigned sp - 48)
    (HspUpper1896 : bv_unsigned sp + 1896 < 0x40000000) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P) -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8CarrierBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  rewrite /writeSuccessTransactionsAt150d8CarrierBlock.
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
  all: destruct H0 as
    (HitemsLength & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      HspAlign & HspLower & HspUpper).
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  subst LET0. subst LET1. subst LET5. subst LET6.
  subst LET10. subst LET13.
  have Hstore32Address :
      bv_unsigned (sp + BV 64 1656)%bv = bv_unsigned sp + 1656 by bv_solve.
  have Hstore8Address :
      bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744 by bv_solve.
  have HauipcValue :
      (Z_to_bv 64 86248 + BV 64 18446744073709531136)%bv =
      BV 64 0x100e8 by bv_solve.
  iRename select ((bv_unsigned (sp + BV 64 1656)%bv) ↦ₘ _)%I
    into "Hstored32".
  iRename select ((bv_unsigned (sp + BV 64 1656)%bv + 4) ↦ₘ? _)%I
    into "Hsuffix32".
  iRename select ((bv_unsigned (sp + BV 64 1744)%bv) ↦ₘ _)%I
    into "Hstored8".
  iRename select ((bv_unsigned (sp + BV 64 1744)%bv + 1) ↦ₘ? _)%I
    into "Hsuffix8".
  iRename select
    ("x1" ↦ᵣ RVal_Bits
      (Z_to_bv 64 86248 + BV 64 18446744073709531136)%bv)%I
    into "Hx1".
  iEval (rewrite Hstore32Address) in "Hstored32 Hsuffix32".
  iEval (rewrite Hstore8Address) in "Hstored8 Hsuffix8".
  iEval (rewrite HauipcValue) in "Hx1".
  have Hsuffix32Address :
      (bv_unsigned sp + 1656 + 4 = bv_unsigned sp + 1660)%Z by lia.
  have Hsuffix32Length :
      (bv_unsigned sp + 1656 + 8 - (bv_unsigned sp + 1660) = 4)%Z by lia.
  have Hsuffix8Address :
      (bv_unsigned sp + 1744 + 1 = bv_unsigned sp + 1745)%Z by lia.
  have Hsuffix8Length :
      (bv_unsigned sp + 1744 + 48 - (bv_unsigned sp + 1745) = 47)%Z by lia.
  iEval (rewrite Hsuffix32Address Hsuffix32Length) in "Hsuffix32".
  iEval (rewrite Hsuffix8Address Hsuffix8Length) in "Hsuffix8".
  rewrite /writeSuccessTransactionsAt150ecCarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  cbn.
  rewrite /writeSuccessTransactionsMachine150ecCarrier /reg_col
    /writeSuccessTransactions150ecCarrierScratch.
  cbn.
  iFrame.
  have Hstored8Value :
      bv_extract 0 8
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 264)) =
      writeSuccessTransactionByte transaction 264 by bv_solve.
  iEval (rewrite Hstored8Value) in "Hstored8".
  have HbyteListFacts :
      writeSuccessTransactionsPost15674ByteListFacts
          sp first second items.
  { repeat split; assumption. }
  iAssert
    (⌜writeSuccessTransactionsPost15674ByteListFacts
        sp first second items⌝)%I as "#HbyteListFacts".
  { iPureIntro. exact HbyteListFacts. }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "#HloadFacts".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items)%I with "[-Hstored8]" as "Hphase".
  { rewrite /writeSuccessTransactionsCurrentPhaseCarrierFrame.
    iFrame. }
  iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Lemma write_success_transactions_carrier_chunk_150d8_to_150ec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P) -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150d8CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hmachine & Harray & Hphase & HloadFacts & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HloadFacts".
  iDestruct "HloadFacts" as
    "(%HtransactionLength & %HbaseAlign & %HbaseLower & %HbaseUpper &
      %HspAlign8 & %HspLower48 & %HspUpper1896 & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof
    (write_success_transactions_carrier_chunk_150d8_to_150ec_raw P sp base
      transaction transactions processed remaining bytes prefix suffix tail
      first second third fourth items HtransactionLength HbaseAlign
      HbaseLower HbaseUpper HspAlign8 HspLower48 HspUpper1896 with
      "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt150d8CarrierBlock.
  iFrame.
Qed.
