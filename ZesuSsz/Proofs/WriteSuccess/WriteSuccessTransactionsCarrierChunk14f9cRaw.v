Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f5c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary14f68.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f98.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f9c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.
#[local] Typeclasses Opaque writeSuccessTransactionsInvariant.

Lemma write_success_transactions_carrier_chunk_14f9c_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fa0 (writeSuccessTransactionsAt14fa0CarrierSpec P) -∗
  instr_body 0x14f9c (writeSuccessTransactionsAt14f9cCarrierSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_14f5c_current_unsigned; try lia.
  all: try (iExists
    (writeSuccessTransactionBytes transaction,
      writeSuccessTransactionByte transaction 265, tt)ₗ).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f5c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f5c_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try apply write_success_14f5c_array_element_address; try lia.
  Unshelve.
  iRename select
    (writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
      True)%I into "HfactsBundle".
  iDestruct "HfactsBundle" as "[Hfacts Htrue]".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & HfactsTrue)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) =
      (base + 288 * Z.of_nat (length processed))%Z by bv_solve.
  iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction)%I into "Harray".
  iDestruct (mem_mapsto_array_region 8%N
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (writeSuccessTransactionBytes transaction) 265 1 with "Harray")
    as "[Hprefix [HbyteArray Hsuffix]]";
    first (rewrite Hlength; lia).
  have HbyteLookup : writeSuccessTransactionBytes transaction !! 265%nat =
      Some (writeSuccessTransactionByte transaction 265) by
    (apply write_success_14f5c_transaction_byte_lookup; lia).
  have HbyteSlice : take 1%nat (drop 265%nat
      (writeSuccessTransactionBytes transaction)) =
      [writeSuccessTransactionByte transaction 265].
  { have Hlookup : drop 265%nat (writeSuccessTransactionBytes transaction) !!
        0%nat = Some (writeSuccessTransactionByte transaction 265) by
      (rewrite lookup_drop; exact HbyteLookup).
    rewrite (take_S_r _ 0%nat _ Hlookup) take_0. reflexivity. }
  iEval (rewrite HbyteSlice mem_mapsto_array_singleton) in "HbyteArray".
  iEval (cbn; rewrite ?HcurrentUnsigned ?Z.add_0_r) in
    "Hprefix HbyteArray Hsuffix".
  iExists
    (writeSuccessTransactionBytes transaction,
      writeSuccessTransactionByte transaction 265, tt)ₗ.
  cbn. rewrite HcurrentUnsigned !Z.add_0_r.
  iFrame "Hprefix HbyteArray Hsuffix".
  repeat iSplit; try iPureIntro; try assumption; try lia; try done.
  liARun.
  iRename select ((_ ↦ₘ∗ take 265
    (writeSuccessTransactionBytes transaction))%I) into "HprefixFinal".
  iRename select ((_ ↦ₘ writeSuccessTransactionByte transaction 265)%I)
    into "HbyteFinal".
  iRename select ((_ ↦ₘ∗ drop 266
    (writeSuccessTransactionBytes transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (base + 288 * Z.of_nat (length processed))
    (writeSuccessTransactionBytes transaction) 265
    (writeSuccessTransactionByte transaction 265)
    (base + 288 * Z.of_nat (length processed) + 266)
    (base + 288 * Z.of_nat (length processed) + 265) with
    "HprefixFinal HsuffixFinal HbyteFinal [] [] []") as "HarrayFinal".
  { iPureIntro. exact HbyteLookup. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  iExists
    (items, fourth, third, second, first, tail, suffix, prefix, bytes,
      remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  iFrame "HarrayFinal".
  iFrame.
  destruct H0 as
    (Hsecond & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      Hsp16Align & Hsp80Lower & HspRamUpper).
  rewrite /writeSuccessTransactions14f98CarrierScratch
    /writeSuccessTransactionsCurrentPhaseCarrierFrame
    /writeSuccessTransactionPhaseEvents /writeSuccessByteArrayOwn
    /writeSuccessTransactionsLoadFacts.
  iFrame.
  repeat iSplit; try (iPureIntro; assumption); try done.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f5c_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
  Unshelve. all: try exact inhabitant.
Qed.
