Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15098.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8TagBridge.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessTransactions150f8CarrierScratchRest
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 16 ∗
   bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ? 8 ∗
   (bv_unsigned sp + 136) ↦ₘ writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 824 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 504 ∗
   (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactions15098X12 transaction ∗
   (bv_unsigned sp + 1648) ↦ₘ
     (bv_or
       (bv_shiftl
         (bv_or
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 280)) (BV 64 24))
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 279)) (BV 64 16)))
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 278)) (BV 64 8))
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 277)))) (BV 64 32))
       (bv_or
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 276)) (BV 64 24))
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 275)) (BV 64 16)))
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 274)) (BV 64 8))
           (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 273))))) ∗
   (bv_unsigned sp + 1656) ↦ₘ
     bv_extract 0 32
       (bv_or
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 284)) (BV 64 24))
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 283)) (BV 64 16)))
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 282)) (BV 64 8))
           (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 281)))) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 ∗
   (bv_unsigned sp + 1745) ↦ₘ? 47 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions150f8CarrierScratchRest) := I.
Global Typeclasses Opaque writeSuccessTransactions150f8CarrierScratchRest.

Lemma write_success_transactions_150f8_carrier_scratch_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150ecCarrierScratch sp base total processed transaction
    first second third fourth items -∗
  writeSuccessTransactions150f8CarrierScratchRest sp base total processed
      transaction first second third fourth items ∗
  (bv_unsigned sp - 32) ↦ₘ? 32 ∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168.
Proof.
  iIntros "Hscratch".
  iEval (unfold writeSuccessTransactions150ecCarrierScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & H120 & H128 & H136 & H144 & H152 & H160 &
      H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 & H232 & H240 &
      H248 & H256 & H264 & H272 & H280 & Hcarrier & H1136 & H1640 & H1648 &
      H1656 & H1660 & Hvalue & Htag & H1680 & H1744 & H1745 & H1792)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hlower") as
    "[Hlower16 HlowerRest]"; first lia.
  iDestruct (mem_mapsto_uninit_split 32 with "HlowerRest") as
    "[Hstack Hupper104]"; first lia.
  have HstackAddr : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
  have HupperAddr : bv_unsigned sp - 48 + 16 + 32 = bv_unsigned sp by lia.
  iEval (rewrite HstackAddr) in "Hstack".
  iEval (rewrite HupperAddr) in "Hupper104".
  iSplitL "Hlower16 Hupper104 Hbase Htotal H120 H128 H136 H144 H152 H160
    H168 H176 H184 H192 H200 H208 H216 H224 H232 H240 H248 H256 H264 H272
    H280 Hcarrier H1136 H1640 H1648 H1656 H1660 H1680 H1744 H1745 H1792".
  - rewrite /writeSuccessTransactions150f8CarrierScratchRest. iFrame.
  - iFrame.
Qed.

Lemma write_success_transactions_150f8_carrier_tag_split
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction) :
  ⌜length (writeSuccessTransactionBytes transaction) = 288%nat⌝ -∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 -∗
  ∃ tagTail,
    (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionByte transaction 168 ∗
    (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
    ⌜bv_to_little_endian 8 8
        (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
      writeSuccessTransactionByte transaction 168 :: tagTail⌝.
Proof.
  iIntros (Hlength) "Htagword".
  have Hdrop : 8%nat <= length (drop 168
      (writeSuccessTransactionBytes transaction)).
  { rewrite length_drop Hlength. lia. }
  have Htake : length
      (take 8 (drop 168 (writeSuccessTransactionBytes transaction))) = 8%nat.
  { rewrite length_take. rewrite Nat.min_l; lia. }
  have Hround :
      bv_to_little_endian 8 8
        (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
      take 8 (drop 168 (writeSuccessTransactionBytes transaction)).
  { apply u64_bytes_roundtrip. exact Htake. }
  destruct (drop 168 (writeSuccessTransactionBytes transaction))
    as [|tag tagTail0] eqn:Hbytes.
  { cbn in Hdrop. lia. }
  have Hlookup : writeSuccessTransactionByte transaction 168 = tag.
  { have Hlookup0 : writeSuccessTransactionBytes transaction !! 168%nat = Some tag.
    { pose proof (lookup_drop (writeSuccessTransactionBytes transaction) 168 0)
        as Hlookup0.
      rewrite Hbytes in Hlookup0. cbn in Hlookup0.
      symmetry. exact Hlookup0. }
    rewrite /writeSuccessTransactionByte Hlookup0. reflexivity. }
  iExists (tl (take 8 (tag :: tagTail0))).
  iPoseProof (write_success_transactions_split_u64_tag
    (bv_unsigned sp + 1672) (writeSuccessTransactionWord transaction 168)
    tag (tl (take 8 (tag :: tagTail0))) with "Htagword") as "Hsplit".
  iSpecialize ("Hsplit" with "[]").
  { iPureIntro. rewrite Hround. cbn. reflexivity. }
  iDestruct "Hsplit" as "(Htag & Htail)".
  have HtailAddr : bv_unsigned sp + 1672 + 1 = bv_unsigned sp + 1673 by lia.
  iEval (rewrite HtailAddr) in "Htail".
  rewrite Hlookup.
  iFrame. iPureIntro.
  rewrite Hround. cbn. reflexivity.
Qed.

Lemma write_success_transactions_150f8_carrier_tag_combine
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction) (tag : bv 8)
    (tagTail : list (bv 8)) :
  (bv_unsigned sp + 1672) ↦ₘ tag -∗
  (bv_unsigned sp + 1673) ↦ₘ∗ tagTail -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
    tag :: tagTail⌝ -∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168.
Proof.
  iIntros "Htag Htail" (Hshape).
  iEval (rewrite -mem_mapsto_array_singleton) in "Htag".
  have HtagAddr : bv_unsigned sp + 1672 + Z.of_N (8 `div` 8) * 1 =
      bv_unsigned sp + 1673 by cbn; lia.
  iEval (rewrite <- HtagAddr) in "Htail".
  iPoseProof (mem_mapsto_array_app_combine 8%N (bv_unsigned sp + 1672)
    (DfracOwn 1) [tag] tagTail with "Htag Htail") as "Harray".
  iPoseProof (mem_mapsto_byte_array_to_mapsto
    (bv_unsigned sp + 1672) (DfracOwn 1) ([tag] ++ tagTail)
    with "Harray") as "Hword".
  have Hlen : length ([tag] ++ tagTail) = 8%nat.
  { pose proof (f_equal (@length (bv 8)) Hshape) as HlenEq.
    rewrite length_bv_to_little_endian in HlenEq; [|lia].
    cbn in HlenEq. symmetry. exact HlenEq. }
  have Hround : Z_to_bv 64 (little_endian_to_bv 8 ([tag] ++ tagTail)) =
      writeSuccessTransactionWord transaction 168.
  { pose proof (Z_to_bv_little_endian_to_bv_to_little_endian 64 8 8
      (writeSuccessTransactionWord transaction 168) ltac:(lia) ltac:(cbn; lia))
      as HroundEq. rewrite Hshape in HroundEq. exact HroundEq. }
  iEval (rewrite Hlen Hround) in "Hword". iExact "Hword".
Qed.
