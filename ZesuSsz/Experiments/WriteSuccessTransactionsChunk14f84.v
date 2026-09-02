From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f84.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f88.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14f68.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.
#[local] Typeclasses Opaque reg_col.

#[local] Hint Rewrite write_success_current_unsigned using lia :
  lithium_rewrite.

Ltac solve_write_success_14f84_current_address :=
  lazymatch goal with
  | Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      apply write_success_array_element_address; [lia | exact Hunsigned]
  end.

Definition writeSuccessTransactionsAt14f84Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine14f84
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f84Block) := I.

Lemma write_success_transactions_chunk_14f84_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f88 (writeSuccessTransactionsAt14f88Spec P) -∗
  instr_body 0x14f84 (writeSuccessTransactionsAt14f84Block P sp base
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
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try solve_write_success_14f84_current_address.
  all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 277 - current)%Z with 277%Z by lia; cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 277, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 277
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction)) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 277]);
        assert (Hbyte :
          drop 277
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 277));
        [ rewrite lookup_drop; cbn;
          apply write_success_transaction_byte_lookup; lia
        | rewrite (take_S_r _ 0 _ Hbyte); rewrite take_0; reflexivity ]
      | ];
      iSplit; [iPureIntro; lia |];
      iIntros "Hbefore Hafter";
      iFrame;
      repeat iSplit; try iPureIntro; try lia;
      try apply write_success_transaction_byte_lookup; try lia;
      liARun
  end.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  1: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      iRename select
        ((current + 0) ↦ₘ∗ take 277
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hprefix277Final";
      iRename select
        (_ ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 277))%I into "Hbyte277Final";
      iRename select
        ((current + 0 + 278%nat) ↦ₘ∗ drop 278
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hsuffix278Final";
      iEval (rewrite Z.add_0_r) in "Hprefix277Final";
      assert (Hsuffix278Address :
          (current + 0 + 278)%Z = (current + 278)%Z) by lia;
      iEval (rewrite Hsuffix278Address) in "Hsuffix278Final";
      assert (Hlookup277Final :
          WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction !! 277%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 277));
      [ apply write_success_transaction_byte_lookup; lia | ];
      iPoseProof (write_success_recombine_transaction_byte current _ 277 _
        Hlookup277Final with
        "Hprefix277Final Hbyte277Final Hsuffix278Final") as "HarrayFinal";
      iRename select (writeSuccessTransactionsCurrentPhaseFrame P sp base
        transaction transactions processed remaining bytes prefix suffix
        tail)%I into "HframeFinal";
      iAssert (writeSuccessTransactionsMachine14f88 sp base transactions
        processed transaction) with "[-HarrayFinal HframeFinal]"
        as "HmachineFinal";
      [ rewrite /writeSuccessTransactionsMachine14f88 /reg_col;
        cbn; iFrame;
        repeat iSplit; try iPureIntro; try reflexivity; try assumption;
          try done | ];
      iExists (tail, suffix, prefix, bytes, remaining, processed,
        transactions, transaction, base, sp, tt)ₗ;
      iFrame "HmachineFinal HarrayFinal HframeFinal";
      rewrite /writeSuccessTransactionsLoadFacts;
      repeat iSplit; try iPureIntro; try assumption; try done
  end.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try assumption.
  all: try reflexivity.
  all: try apply write_success_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.

Lemma write_success_transactions_chunk_14f84
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f88 (writeSuccessTransactionsAt14f88Spec P) -∗
  instr_body 0x14f84 (writeSuccessTransactionsAt14f84Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f84Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f84_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f84Block.
  iAssert (writeSuccessTransactionsLoadFacts sp base transaction processed
    bytes) as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iFrame "Hmachine Harray Hframe HfactsFinal".
  iSplit.
  - iPureIntro. apply write_success_current_unsigned; lia.
  - done.
Qed.
