From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f34.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f38.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.
#[local] Typeclasses Opaque writeSuccessTransactionsInvariant.

Lemma write_success_transactions_carrier_chunk_14f34
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f38 (writeSuccessTransactionsAt14f38CarrierSpec P) -∗
  instr_body 0x14f34 (writeSuccessTransactionsAt14f34CarrierSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: iExists
    (writeSuccessTransactionBytes transaction,
      writeSuccessTransactionWord transaction 144, tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iRename select
    (writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
      True)%I into "HfactsBundle".
  iDestruct "HfactsBundle" as "[Hfacts Htrue]".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HfactsCopy".
  iDestruct "HfactsCopy" as "[%Hlength HfactsRest]".
  iDestruct "HfactsRest" as
    "(%HcurrentAlign & %HcurrentLower & %HcurrentUpper & HspFacts)".
  iDestruct "HspFacts" as "[%HspAlign HspFacts]".
  iDestruct "HspFacts" as "[%HspLower HspFacts]".
  iDestruct "HspFacts" as "[%HspUpper HspTrue]".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) =
      (base + 288 * Z.of_nat (length processed))%Z by bv_solve.
  iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction)%I into "Harray".
  iDestruct (mem_mapsto_array_region 8%N
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (writeSuccessTransactionBytes transaction) 144 8 with "Harray")
    as "[Hprefix [HwordBytes Hsuffix]]"; first (rewrite Hlength; lia).
  iDestruct (mem_mapsto_byte_array_to_mapsto with "HwordBytes") as "Hword".
  have HwordLength : length (take 8 (drop 144
    (writeSuccessTransactionBytes transaction))) = 8%nat by
    (rewrite length_take length_drop Hlength; lia).
  iEval (rewrite HwordLength) in "Hword".
  have HarrayOffset : (Z.of_N (8 `div` 8) * 144 = 144)%Z by vm_compute.
  have HarrayWidth : (Z.to_N 8 * 8 = 64)%N by vm_compute.
  iEval (rewrite HarrayOffset HarrayWidth) in "Hword".
  iEval (cbn; rewrite ?Z.add_0_r) in "Hprefix Hword Hsuffix".
  iEval (cbn; rewrite HcurrentUnsigned).
  rewrite /writeSuccessTransactionWord.
  rewrite !Z.add_0_r.
  iFrame "Hprefix Hword Hsuffix".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  iRename select ((_ ↦ₘ∗ take 144
    (writeSuccessTransactionBytes transaction))%I) into "HprefixFinal".
  iRename select ((_ ↦ₘ Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop 144 (writeSuccessTransactionBytes transaction)))))%I)
    into "HwordFinal".
  iRename select ((_ ↦ₘ∗ drop 152
    (writeSuccessTransactionBytes transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (writeSuccessTransactionBytes transaction) 144
    (base + 288 * Z.of_nat (length processed) + 152)
    (base + 288 * Z.of_nat (length processed) + 144) with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite Hlength. lia. }
  iRename select (writeSuccessTransactionRestOwn transaction ∗ _)%I
    into "HphaseRest".
  iDestruct "HphaseRest" as "[Hrest HphaseRest]".
  iDestruct "HphaseRest" as "[Hremaining HphaseRest]".
  iDestruct "HphaseRest" as "[Hmmio HphaseRest]".
  iDestruct "HphaseRest" as "[Htrace HphaseRest]".
  iDestruct "HphaseRest" as "[HP HphaseRest]".
  iDestruct "HphaseRest" as "[Hinv HphaseRest]".
  iDestruct "HphaseRest" as "[Hexit HphaseTrue]".
  iRename select (base ↦ₘ∗ prefix)%I into "HbasePrefix".
  iRename select
    ((base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
      writeSuccessTransactionsBytes remaining)%I into "HbaseSuffix".
  iRename select (writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  iRename select
    ((match writeSuccessTransactionData transaction with
      | [] => _
      | _ :: _ => _
      end)%I) into "Hdata".
  iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items)%I with
    "[HbasePrefix HbaseSuffix Hprocessed Hdata Hrest Hremaining Hmmio Htrace
      HP Hinv Hexit HphaseTrue]" as "Hphase".
  { rewrite /writeSuccessTransactionsCurrentPhaseCarrierFrame
      /writeSuccessTransactionPhaseEvents /writeSuccessByteArrayOwn.
    iFrame. }
  iEval (unfold writeSuccessTransactionsAt14f38CarrierSpec).
  iExists
    (items, fourth, third, second, first, tail, suffix, prefix, bytes,
      remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  cbn.
  rewrite /writeSuccessTransactions14f34CarrierScratch.
  iFrame "HarrayFinal".
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try done.
  iRename select
    (((∃ vact : valu, ⌜valu_has_shape vact (BitsShape 64)⌝ ∗
      "x1" ↦ᵣ vact) ∗ _)%I) into "Hregs".
  iDestruct "Hregs" as
    "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & H12 & H13 & H14 & H15 & H16 &
      H17 & H18 & H19 & H20 & H21 & H22 & H26 & H27 & H28 & H29 & H30 &
      H31 & Hemp)".
  iFrame.
Qed.
