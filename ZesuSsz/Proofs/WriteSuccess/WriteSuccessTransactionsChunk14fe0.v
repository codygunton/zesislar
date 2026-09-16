Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fe0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fe0Loads.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14fe0_byte_lookup
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (index : nat) :
  (index < length
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction))%nat ->
  WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction !! index =
    Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction index).
Proof.
  intros Hindex.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
    transaction !! index) eqn:Hlookup; [done |].
  apply lookup_ge_None_1 in Hlookup. lia.
Qed.

Lemma write_success_transactions_chunk_14fe0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fe4 (writeSuccessTransactionsAt14fe4Spec P) -∗
  instr_body 0x14fe0 (writeSuccessTransactionsAt14fe0Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iEval (unfold InstrSpecs.Lookup.instr_body_lookup_resources) in "Hcode".
  iPoseProof ("Hcode" $! 0x14fe0
    (zesu_lbu_byte_array_at_spec 0x14fe0 "x7" "x10" 268 0 268)
    with "[]") as "Hlbu".
  { iPureIntro.
    exact IslaTraces.write_success_blocks.Index.body_lookup_a14fe0. }
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14fe0Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed by bv_solve.
  iEval (unfold writeSuccessTransactionsMachine14fe0) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10 &
      Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 &
      Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx28 & Hx29 & Hx30 & Hx31 &
      Hscratch & _)".
  iEval (unfold writeSuccessTransactionsScratch14fc8) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hstack0 & Hstack104 & Hstack112 & Hstack120 & Hstack128 & Hstack224 &
      Hstack232 & Hstack240 & Hstack248 & Hstack256 & Hstack272 & Hstack280 &
      Hstack1664 & Hstack1672 & Hstack1680 & _)".
  have HbyteLookup :
    WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction !!
      268%nat =
    Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 268).
  { apply write_success_14fe0_byte_lookup. lia. }
  iDestruct (mem_mapsto_array_region 8
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    268 1 with "Harray") as "(Hprefix & HbyteArray & Hsuffix)".
  { rewrite Hlength. lia. }
  have HbyteTake :
    take 1 (drop 268
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction)) =
    [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 268].
  { assert (HdropLookup :
      drop 268
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction) !! 0%nat =
      Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 268)).
    { rewrite lookup_drop. cbn. exact HbyteLookup. }
    rewrite (take_S_r _ 0 _ HdropLookup). rewrite take_0. reflexivity. }
  iEval (rewrite HbyteTake mem_mapsto_array_singleton) in "HbyteArray".
  have HprefixAddress :
    (base + 288 * length processed =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 0)%Z.
  { rewrite HcurrentUnsigned. lia. }
  have HbyteAddress :
    (base + 288 * length processed + Z.of_N (8 `div` 8) * 268%nat =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 268)%Z.
  { rewrite HcurrentUnsigned. vm_compute. lia. }
  have HsuffixAddress :
    (base + 288 * length processed + Z.of_N (8 `div` 8) * (268 + 1)%nat =
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) + 0 +
        Z.of_nat (268 + 1))%Z.
  { rewrite HcurrentUnsigned.
    replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity.
    replace (Z.of_nat (268 + 1)) with 269%Z by reflexivity.
    lia. }
  iEval (rewrite HprefixAddress) in "Hprefix".
  iEval (rewrite HbyteAddress) in "HbyteArray".
  iEval (rewrite HsuffixAddress) in "Hsuffix".
  iAssert ("x7" ↦ᵣ: fun _ => True)%I with "[Hx7]" as "Hx7Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx7". done. }
  iApply "Hlbu".
  rewrite /zesu_lbu_byte_array_at_spec.
  iExists (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 268),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction).
  iFrame "Hsys Hx7Any Hx10 HbyteArray Hprefix Hsuffix".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & Hx7Post & Hx10Post & HbytePost &
      HprefixPost & HsuffixPost & _)".
  iEval (rewrite ?HcurrentUnsigned ?Z.add_0_r) in
    "HbytePost HprefixPost HsuffixPost".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    268
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 268)
    (base + 288 * Z.of_nat (length processed) + 269)
    (base + 288 * Z.of_nat (length processed) + 268) with
    "HprefixPost HsuffixPost HbytePost [] [] []") as "HarrayFinal".
  { iPureIntro. exact HbyteLookup. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  iAssert (writeSuccessTransactions14fe0LoadFrame
    sp base transactions processed transaction)%I
    with "[Hother Hx2 Hx5 Hx6 Hx8 Hx9 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16
      Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25 Hx26 Hx31 Hstack0 Hstack104
      Hstack112 Hstack120 Hstack128 Hstack224 Hstack232 Hstack240 Hstack248
      Hstack256 Hstack272 Hstack280 Hstack1664 Hstack1672 Hstack1680]"
    as "HloadFrame".
  { rewrite /writeSuccessTransactions14fe0LoadFrame
      /writeSuccessTransactionsScratch14fc8.
    iFrame. }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt14fe4Spec
    /writeSuccessTransactionsAt14fe0LoadSpec.
  iExists transaction, sp, base, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HsysPost Hx10Post Hx7Post Hx28 Hx29 Hx30 HloadFrame HarrayFinal
    Hframe HfactsFinal".
Qed.
