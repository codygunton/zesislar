From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f9c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fa0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f68.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.
#[local] Typeclasses Opaque reg_col.

#[local] Hint Rewrite write_success_current_unsigned using lia :
  lithium_rewrite.

Ltac solve_write_success_14f9c_current_address :=
  lazymatch goal with
  | Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      apply write_success_array_element_address; [lia | exact Hunsigned]
  end.

Definition writeSuccessTransactionsAt14f9cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine14f9c
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f9cBlock) := I.

Lemma write_success_transactions_chunk_14f9c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fa0 (writeSuccessTransactionsAt14fa0Spec P) -∗
  instr_body 0x14f9c (writeSuccessTransactionsAt14f9cBlock P sp base
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
  all: try solve_write_success_14f9c_current_address.
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
      replace (current + 265 - current)%Z with 265%Z by lia; cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 265, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 265
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction)) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265]);
        assert (Hbyte :
          drop 265
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265));
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
        ((current + 0) ↦ₘ∗ take 265
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hprefix265Final";
      iRename select
        (_ ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265))%I into "Hbyte265Final";
      iRename select
        ((current + 0 + 266%nat) ↦ₘ∗ drop 266
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hsuffix266Final";
      iEval (rewrite Z.add_0_r) in "Hprefix265Final";
      assert (Hsuffix266Address :
          (current + 0 + 266)%Z = (current + 266)%Z) by lia;
      iEval (rewrite Hsuffix266Address) in "Hsuffix266Final";
      assert (Hlookup265Final :
          WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction !! 265%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265));
      [ apply write_success_transaction_byte_lookup; lia | ];
      iPoseProof (write_success_recombine_transaction_byte current _ 265 _
        Hlookup265Final with
        "Hprefix265Final Hbyte265Final Hsuffix266Final") as "HarrayFinal";
      iRename select (writeSuccessTransactionsCurrentPhaseFrame P sp base
        transaction transactions processed remaining bytes prefix suffix
        tail)%I into "HframeFinal";
      iAssert (writeSuccessTransactionsMachine14fa0 sp base transactions
        processed transaction) with "[-HarrayFinal HframeFinal]"
        as "HmachineFinal";
      [ rewrite /writeSuccessTransactionsMachine14fa0 /reg_col;
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
Lemma write_success_transactions_chunk_14f9c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fa0 (writeSuccessTransactionsAt14fa0Spec P) -∗
  instr_body 0x14f9c (writeSuccessTransactionsAt14f9cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f9cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f9c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f9cBlock.
  iAssert (writeSuccessTransactionsLoadFacts sp base transaction processed
    bytes) as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iFrame "Hmachine Harray Hframe HfactsFinal".
  iSplit.
  - iPureIntro. apply write_success_current_unsigned; lia.
  - done.
Qed.
