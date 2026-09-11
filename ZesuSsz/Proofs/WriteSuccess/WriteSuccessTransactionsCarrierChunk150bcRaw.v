Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150bc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150c0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15044Load.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions150bcCarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions150bcCarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions150bcCarrierPhase) := I.
Local Remove Hints writeSuccessTransactions150bcCarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions150bcCarrierPhase.

Definition writeSuccessTransactionsAt150bcCarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine150bcCarrier sp base transactions processed
     transaction first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions150bcCarrierPhase P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150bcCarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_150bc_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150c0 (writeSuccessTransactionsAt150c0CarrierSpec P) -∗
  instr_body 0x150bc (writeSuccessTransactionsAt150bcCarrierBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15044_current_unsigned; try lia.
  all: iExists (writeSuccessTransactionBytes transaction, tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15044_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists (writeSuccessTransactionBytes transaction, tt)ₗ.
  iIntros "Hprefix240 Hsuffix248".
  cbn.
  have Hstart240 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 240 -
         (base + 288 * Z.of_nat (length processed))) = 240%nat.
  { rewrite write_success_15044_current_unsigned; lia. }
  iEval (rewrite Hstart240) in "Hprefix240 Hsuffix248".
  rewrite Hstart240 write_success_15044_current_unsigned; try lia.
  replace (base + 288 * Z.of_nat (length processed) + 0)%Z with
    (base + 288 * Z.of_nat (length processed))%Z by lia.
  iFrame "Hprefix240 Hsuffix248".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iRename select
    ((_ ↦ₘ∗ take 240 (writeSuccessTransactionBytes transaction))%I)
    into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 240 (writeSuccessTransactionBytes transaction)))))%I)
    into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 248 (writeSuccessTransactionBytes transaction))%I)
    into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (writeSuccessTransactionBytes transaction) 240 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H1. lia. }
  iRename select
    (writeSuccessTransactions150bcCarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I into "HframeFinal".
  iEval (unfold writeSuccessTransactions150bcCarrierPhase) in "HframeFinal".
  rewrite /writeSuccessTransactionsAt150c0CarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  cbn.
  iFrame "HframeFinal HarrayFinal".
  rewrite /writeSuccessTransactionsMachine150c0Carrier /reg_col
    /writeSuccessTransactions150c0CarrierScratch.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  all: destruct H0 as
    (HitemsLength & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      HspAlign & HspLower & HspUpper); assumption.
Qed.
Lemma write_success_transactions_carrier_chunk_150bc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150c0 (writeSuccessTransactionsAt150c0CarrierSpec P) -∗
  instr_body 0x150bc (writeSuccessTransactionsAt150bcCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150bcCarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_150bc_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt150bcCarrierBlock
    /writeSuccessTransactions150bcCarrierPhase.
  iDestruct "Hentry" as "(Hmachine & Harray & Hphase & Hfacts & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  iDestruct "Hfacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %HspAlign & %HspLower &
      %HspUpper & _)".
  iFrame "Hmachine Harray Hphase".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  apply write_success_15044_current_unsigned; lia.
Qed.
