From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fe0Loads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fe0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.
#[local] Typeclasses Opaque writeSuccessTransactions14fe0LoadFrame.

Lemma write_success_transactions_chunk_14fec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14ff0 (writeSuccessTransactionsAt14ff0Spec P) -∗
  instr_body 0x14fec (writeSuccessTransactionsAt14fecSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iEval (unfold InstrSpecs.Lookup.instr_body_lookup_resources) in "Hcode".
  iPoseProof ("Hcode" $! 0x14fec
    (zesu_lbu_byte_array_at_spec 0x14fec "x30" "x10" 271 0 271)
    with "[]") as "Hlbu".
  { iPureIntro.
    exact IslaTraces.write_success_blocks.Index.body_lookup_a14fec. }
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14fecSpec
    /writeSuccessTransactionsAt14fe0LoadSpec.
  iDestruct "Hentry" as
    (transaction sp base transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx10 & Hx7 & Hx28 & Hx29 & Hx30 & HloadFrame & Harray &
      Hphase & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed by bv_solve.
  have HbyteLookup :
    WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction !!
      271%nat =
    Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 271).
  { apply write_success_14fe0_byte_lookup. lia. }
  iDestruct (mem_mapsto_array_region 8
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    271 1 with "Harray") as "(Hprefix & HbyteArray & Hsuffix)".
  { rewrite Hlength. lia. }
  have HbyteTake :
    take 1 (drop 271
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction)) =
    [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 271].
  { assert (HdropLookup :
      drop 271
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction) !! 0%nat =
      Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 271)).
    { rewrite lookup_drop. cbn. exact HbyteLookup. }
    rewrite (take_S_r _ 0 _ HdropLookup). rewrite take_0. reflexivity. }
  iEval (rewrite HbyteTake mem_mapsto_array_singleton) in "HbyteArray".
  have HprefixAddress :
    (base + 288 * length processed =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 0)%Z.
  { rewrite HcurrentUnsigned. lia. }
  have HbyteAddress :
    (base + 288 * length processed + Z.of_N (8 `div` 8) * 271%nat =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 271)%Z.
  { rewrite HcurrentUnsigned. vm_compute. lia. }
  have HsuffixAddress :
    (base + 288 * length processed + Z.of_N (8 `div` 8) * (271 + 1)%nat =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 0 +
        Z.of_nat (271 + 1))%Z.
  { rewrite HcurrentUnsigned.
    replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity.
    replace (Z.of_nat (271 + 1)) with 272%Z by reflexivity.
    lia. }
  iEval (rewrite HprefixAddress) in "Hprefix".
  iEval (rewrite HbyteAddress) in "HbyteArray".
  iEval (rewrite HsuffixAddress) in "Hsuffix".
  iAssert ("x30" ↦ᵣ: fun _ => True)%I with "[Hx30]" as "Hx30Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx30". done. }
  iApply "Hlbu".
  rewrite /zesu_lbu_byte_array_at_spec.
  iExists (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 271),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction).
  iFrame "Hsys Hx30Any Hx10 HbyteArray Hprefix Hsuffix".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & Hx30Post & Hx10Post & HbytePost &
      HprefixPost & HsuffixPost & _)".
  iEval (rewrite ?HcurrentUnsigned ?Z.add_0_r) in
    "HbytePost HprefixPost HsuffixPost".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    271
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 271)
    (base + 288 * Z.of_nat (length processed) + 272)
    (base + 288 * Z.of_nat (length processed) + 271) with
    "HprefixPost HsuffixPost HbytePost [] [] []") as "HarrayFinal".
  { iPureIntro. exact HbyteLookup. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt14ff0Spec
    /writeSuccessTransactionsAt14fe0LoadSpec.
  iExists transaction, sp, base, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HsysPost Hx10Post Hx7 Hx28 Hx29 Hx30Post HloadFrame HarrayFinal
    Hphase HfactsFinal".
Qed.
