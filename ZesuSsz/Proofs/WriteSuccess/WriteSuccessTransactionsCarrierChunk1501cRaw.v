From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1501c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState1501c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15020.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1501c.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions1501cCarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions1501cCarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions1501cCarrierPhase) := I.
Local Remove Hints writeSuccessTransactions1501cCarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions1501cCarrierPhase.

Definition writeSuccessTransactionsAt1501cCarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x18" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x20" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x29" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
    "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
    "x29" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 64) -∗
    writeSuccessTransactionsMachine15028Carrier sp base transactions processed
      transaction first second third fourth items) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions1501cCarrierPhase P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt1501cCarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_1501c_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020CarrierSpec P) -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cCarrierBlock P sp base
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
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix48 Hsuffix56".
  cbn.
  have Hstart48 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 48 -
         (base + 288 * Z.of_nat (length processed))) = 48%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart48) in "Hprefix48 Hsuffix56".
  rewrite Hstart48 H7 !Z.add_0_r.
  iFrame "Hprefix48 Hsuffix56".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  all: try (rewrite H7; rewrite length_drop; rewrite H0; lia).
  iRename select
    ((_ ↦ₘ∗ take 48
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 48
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 56
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    48 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactions1501cCarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I
    into "HframeFinal".
  iEval (unfold writeSuccessTransactions1501cCarrierPhase) in "HframeFinal".
  iRename select ("x20" ↦ᵣ RVal_Bits _)%I into "Hx20Exact".
  iRename select ("x29" ↦ᵣ RVal_Bits _)%I into "Hx29Exact".
  iAssert ("x20" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[Hx20Exact]" as "Hx20Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx20Exact".
    iPureIntro. done. }
  iAssert ("x29" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[Hx29Exact]" as "Hx29Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx29Exact".
    iPureIntro. done. }
  rewrite /writeSuccessTransactionsAt15020CarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, transactions, transaction, sp, tt)ₗ.
  cbn.
  iFrame "Hx20Shape Hx29Shape HframeFinal HarrayFinal".
  rewrite /reg_col.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
