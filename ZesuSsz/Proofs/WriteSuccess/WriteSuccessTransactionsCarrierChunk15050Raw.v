From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15050.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15054.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15044Load.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions15050CarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions15050CarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions15050CarrierPhase) := I.
Local Remove Hints writeSuccessTransactions15050CarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions15050CarrierPhase.

Definition writeSuccessTransactionsAt15050CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine15050Carrier sp base transactions processed
     transaction first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions15050CarrierPhase P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt15050CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_15050_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054CarrierSpec P) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050CarrierBlock P sp base
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
  iIntros "Hprefix88 Hsuffix96".
  cbn.
  have Hstart88 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 88 -
         (base + 288 * Z.of_nat (length processed))) = 88%nat.
  { rewrite write_success_15044_current_unsigned; lia. }
  iEval (rewrite Hstart88) in "Hprefix88 Hsuffix96".
  rewrite Hstart88 write_success_15044_current_unsigned; try lia.
  replace (base + 288 * Z.of_nat (length processed) + 0)%Z with
    (base + 288 * Z.of_nat (length processed))%Z by lia.
  iFrame "Hprefix88 Hsuffix96".
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
    ((_ ↦ₘ∗ take 88 (writeSuccessTransactionBytes transaction))%I)
    into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 88 (writeSuccessTransactionBytes transaction)))))%I)
    into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 96 (writeSuccessTransactionBytes transaction))%I)
    into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (writeSuccessTransactionBytes transaction) 88 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H1. lia. }
  iRename select
    (writeSuccessTransactions15050CarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I into "HframeFinal".
  iEval (unfold writeSuccessTransactions15050CarrierPhase) in "HframeFinal".
  rewrite /writeSuccessTransactionsAt15054CarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  cbn.
  iFrame "HframeFinal HarrayFinal".
  rewrite /writeSuccessTransactionsMachine15054Carrier /reg_col
    /writeSuccessTransactions15054CarrierScratch.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  all: destruct H0 as
    (HitemsLength & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      HspAlign & HspLower & HspUpper); assumption.
Qed.

Lemma write_success_transactions_carrier_chunk_15050
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054CarrierSpec P) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15050CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_15050_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt15050CarrierBlock
    /writeSuccessTransactions15050CarrierPhase.
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
