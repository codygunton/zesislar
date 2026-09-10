From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f20.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14f1c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_14f1c_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt14f1cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x25" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ ([] : list (bv 8)) ∗
   writeSuccessTransactions14f1cFrame sp base transactions processed ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f1cBlock) := I.

Lemma write_success_transactions_chunk_14f1c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f20 (writeSuccessTransactionsAt14f20Spec P) -∗
  instr_body 0x14f1c (writeSuccessTransactionsAt14f1cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_14f1c_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      Z_to_bv 64 (little_endian_to_bv 8
        (take 8
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))), tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f1c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "Harray".
  all: iDestruct (mem_mapsto_array_region 8%N
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    0 8 with "Harray") as "[Hprefix [HwordBytes Hsuffix]]".
  all: try (rewrite H0; lia).
  all: iDestruct (mem_mapsto_byte_array_to_mapsto with "HwordBytes")
    as "Hword".
  all: have HwordLength :
    length (take 8 (drop 0
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))) = 8%nat by (rewrite length_take length_drop H0; lia).
  all: iEval (rewrite HwordLength) in "Hword".
  all: have HarrayOffset :
    (Z.of_N (8 `div` 8) * 0 = 0)%Z by vm_compute.
  all: have HarrayWidth :
    (Z.to_N 8 * 8 = 64)%N by vm_compute.
  all: iEval
    (rewrite HarrayOffset HarrayWidth drop_0 Z.add_0_r) in "Hword".
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      Z_to_bv 64 (little_endian_to_bv 8
        (take 8
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))), tt)ₗ.
  iAssert
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      take 0
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction))%I with "[Hprefix]" as "HprefixNormalized".
  { iExact "Hprefix". }
  iAssert
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ
      Z_to_bv 64 (little_endian_to_bv 8
        (take 8
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))))%I with "[Hword]" as "HwordNormalized".
  { iExact "Hword". }
  iAssert
    ((base + 288 * Z.of_nat (length processed) + 8) ↦ₘ∗
      drop 8
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction))%I with "[Hsuffix]" as "HsuffixNormalized".
  { iExact "Hsuffix". }
  all: iEval (cbn; rewrite H7).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f1c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iSplit.
  { iPureIntro. rewrite take_0. done. }
  rewrite !Z.add_0_r drop_0.
  iFrame "HwordNormalized HsuffixNormalized".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ
      Z_to_bv 64 (little_endian_to_bv 8
        (take 8
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))))%I into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 8
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    0 _ _ with
    "HprefixNormalized HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  iSplit.
  { iPureIntro. rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      drop_0. done. }
  cbn.
  iFrame "HarrayFinal".
  iFrame.
  repeat iSplit; try (iPureIntro; assumption).
  all: try done.
Qed.

Lemma write_success_transactions_chunk_14f1c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f20 (writeSuccessTransactionsAt14f20Spec P) -∗
  instr_body 0x14f1c (writeSuccessTransactionsAt14f1cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f1cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx10 & Harray & Hempty & Hmachine & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f1c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f1cBlock.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_14f1c_current_unsigned; lia.
Qed.
