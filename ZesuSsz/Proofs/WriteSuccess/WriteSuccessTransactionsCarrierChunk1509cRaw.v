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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState1509c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150a0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15044Load.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions1509cCarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions1509cCarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions1509cCarrierPhase) := I.
Local Remove Hints writeSuccessTransactions1509cCarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions1509cCarrierPhase.

Definition writeSuccessTransactionsAt1509cCarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine1509cCarrier sp base transactions processed
     transaction first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions1509cCarrierPhase P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt1509cCarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_1509c_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150a0 (writeSuccessTransactionsAt150a0CarrierSpec P) -∗
  instr_body 0x1509c (writeSuccessTransactionsAt1509cCarrierBlock P sp base
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
  iIntros "Hprefix200 Hsuffix208".
  cbn.
  have Hstart200 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 200 -
         (base + 288 * Z.of_nat (length processed))) = 200%nat.
  { rewrite write_success_15044_current_unsigned; lia. }
  iEval (rewrite Hstart200) in "Hprefix200 Hsuffix208".
  rewrite ?Hstart200 ?write_success_15044_current_unsigned; try lia.
  replace (base + 288 * Z.of_nat (length processed) + 0)%Z with
    (base + 288 * Z.of_nat (length processed))%Z by lia.
  iFrame "Hprefix200 Hsuffix208".
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
    ((_ ↦ₘ∗ take 200 (writeSuccessTransactionBytes transaction))%I)
    into "HprefixFinal".
  iRename select ((_ ↦ₘ Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop _ (writeSuccessTransactionBytes transaction)))))%I) into "HwordFinal";
    iEval (rewrite (zesu_integer_array_byte_equality (base + 288 * Z.of_nat (length processed)) 200 (writeSuccessTransactionBytes transaction))) in "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 208 (writeSuccessTransactionBytes transaction))%I)
    into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (writeSuccessTransactionBytes transaction) 200 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H1. lia. }
  iRename select
    (writeSuccessTransactions1509cCarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I into "HframeFinal".
  iEval (unfold writeSuccessTransactions1509cCarrierPhase) in "HframeFinal".
  rewrite /writeSuccessTransactionsAt150a0CarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  cbn.
  iFrame "HframeFinal HarrayFinal".
  rewrite /writeSuccessTransactionsMachine150a0Carrier /reg_col
    /writeSuccessTransactions150a0CarrierScratch.
  cbn. iRename select ("x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop _ (writeSuccessTransactionBytes transaction))))))%I into "HregisterFinal";
    iEval (rewrite (zesu_integer_array_byte_equality (base + 288 * Z.of_nat (length processed)) 200 (writeSuccessTransactionBytes transaction))) in "HregisterFinal"; iFrame "HregisterFinal"; iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  all: lazymatch goal with Hfacts :
    WriteSuccessTransactionsPost15674Boundary.writeSuccessTransactionsPost15674ByteListFacts _ _ _ _ |- _ =>
    destruct Hfacts as (HitemsLength & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper & HspAlign & HspLower & HspUpper) end; assumption.
Qed.
Lemma write_success_transactions_carrier_chunk_1509c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150a0 (writeSuccessTransactionsAt150a0CarrierSpec P) -∗
  instr_body 0x1509c (writeSuccessTransactionsAt1509cCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1509cCarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_1509c_raw P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt1509cCarrierBlock
    /writeSuccessTransactions1509cCarrierPhase.
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
