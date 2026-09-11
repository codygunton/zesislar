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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1501c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState1501c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15020.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15024.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1501c.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactions15020CarrierPhase
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.

Global Instance writeSuccessTransactions15020CarrierPhase_unfold :
    LithiumUnfold (@writeSuccessTransactions15020CarrierPhase) := I.
Local Remove Hints writeSuccessTransactions15020CarrierPhase_unfold :
  typeclass_instances.
#[local] Typeclasses Opaque writeSuccessTransactions15020CarrierPhase.

Definition writeSuccessTransactionsAt15020CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
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
   writeSuccessTransactions15020CarrierPhase P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt15020CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_15020_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024CarrierSpec P) -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020CarrierBlock P sp base
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
  iIntros "Hprefix56 Hsuffix64".
  cbn.
  have Hstart56 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 56 -
         (base + 288 * Z.of_nat (length processed))) = 56%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart56) in "Hprefix56 Hsuffix64".
  rewrite Hstart56 H7 !Z.add_0_r.
  iFrame "Hprefix56 Hsuffix64".
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
    ((_ ↦ₘ∗ take 56
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 56
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    56 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactions15020CarrierPhase P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I
    into "HframeFinal".
  iEval (unfold writeSuccessTransactions15020CarrierPhase) in "HframeFinal".
  rewrite /writeSuccessTransactionsAt15024CarrierSpec.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, transactions, sp, tt)ₗ.
  cbn.
  iFrame "HframeFinal HarrayFinal".
  rewrite /reg_col.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
