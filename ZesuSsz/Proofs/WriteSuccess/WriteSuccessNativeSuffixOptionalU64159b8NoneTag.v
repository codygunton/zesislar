From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8TagBridge.

Lemma write_success_suffix_optional_u64_tag_bytes (tag : bv 64) :
  ∃ tail,
    bv_to_little_endian 8 8 (bv_unsigned tag) =
      bv_extract 0 8 tag :: tail.
Proof.
  have Hlookup :
      bv_to_little_endian 8 8 (bv_unsigned tag) !! 0%nat =
        Some (bv_extract 0 8 tag).
  { apply (proj2 (bv_to_little_endian_lookup_Some 8 8
      (bv_unsigned tag) 0 (bv_extract 0 8 tag) ltac:(lia))).
    split; first lia. apply bv_eq. bv_solve. }
  destruct (bv_to_little_endian 8 8 (bv_unsigned tag)) as [|byte tail]
    eqn:Hbytes; cbn in Hlookup; [done |].
  injection Hlookup as ->. eauto.
Qed.

Lemma write_success_suffix_optional_u64_tag_split
    `{!islaG Sigma} `{!threadG} (address : Z) (tag : bv 64) :
  address ↦ₘ tag -∗
  ∃ tail,
    address ↦ₘ bv_extract 0 8 tag ∗
    (address + 1) ↦ₘ∗ tail ∗
    ⌜bv_to_little_endian 8 8 (bv_unsigned tag) =
      bv_extract 0 8 tag :: tail⌝.
Proof.
  iIntros "Htag".
  destruct (write_success_suffix_optional_u64_tag_bytes tag) as (tail & Hshape).
  iPoseProof (write_success_transactions_split_u64_tag address tag
    (bv_extract 0 8 tag) tail with "Htag []") as "Hsplit".
  { iPureIntro. exact Hshape. }
  iDestruct "Hsplit" as "(Hbyte & Htail)".
  iExists tail. iFrame. iPureIntro. exact Hshape.
Qed.

Lemma write_success_suffix_optional_u64_tag_combine
    `{!islaG Sigma} `{!threadG} (address : Z) (tag : bv 64)
    (tail : list (bv 8)) :
  address ↦ₘ bv_extract 0 8 tag -∗
  (address + 1) ↦ₘ∗ tail -∗
  ⌜bv_to_little_endian 8 8 (bv_unsigned tag) =
    bv_extract 0 8 tag :: tail⌝ -∗
  address ↦ₘ tag.
Proof.
  iIntros "Hbyte Htail" (Hshape).
  iAssert (address ↦ₘ∗ (bv_extract 0 8 tag :: tail))%I
    with "[Hbyte Htail]" as "Hbytes".
  { iEval (rewrite <- mem_mapsto_array_singleton) in "Hbyte".
    iApply (mem_mapsto_array_app_combine 8%N address (DfracOwn 1)
      [bv_extract 0 8 tag] tail with "Hbyte").
    cbn. iExact "Htail". }
  iDestruct (mem_mapsto_byte_array_to_mapsto with "Hbytes") as "Htag".
  have Hlen : length (bv_extract 0 8 tag :: tail) = 8%nat.
  { pose proof (f_equal (@length (bv 8)) Hshape) as HlenEq.
    rewrite length_bv_to_little_endian in HlenEq; [|lia].
    cbn in HlenEq. symmetry. exact HlenEq. }
  have Hround :
      Z_to_bv 64 (little_endian_to_bv 8
        (bv_extract 0 8 tag :: tail)) = tag.
  { pose proof (Z_to_bv_little_endian_to_bv_to_little_endian
      64 8 8 tag ltac:(lia) ltac:(cbn; lia)) as HroundEq.
    rewrite Hshape in HroundEq. exact HroundEq. }
  iEval (rewrite Hlen Hround) in "Htag".
  iExact "Htag".
Qed.
