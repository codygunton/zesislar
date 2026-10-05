From Coq Require Import List Lia ZArith.
From stdpp Require Import bitvector.definitions list_numbers.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.PureFacts.

Import ListNotations.
Open Scope Z_scope.

Lemma littleEndian_machine_bytes count z :
  0 <= z < 2 ^ (8 * Z.of_nat count) ->
  littleEndian (bv_to_little_endian (Z.of_nat count) 8 z) = z.
Proof.
  revert z. induction count as [|count IH]; intros z Hz.
  - replace z with 0 by (simpl in Hz; lia).
    reflexivity.
  - rewrite Nat2Z.inj_succ.
    unfold bv_to_little_endian at 1.
    rewrite Z_to_little_endian_succ by lia.
    simpl.
    rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    rewrite Z_to_bv_small by
      (unfold bv_modulus; cbn; apply Z.mod_pos_bound; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 8) with 256.
    change (list_fmap Z (bv 8) (fun b => Z_to_bv 8 b)
      (Z_to_little_endian (Z.of_nat count) 8 (z / 256))) with
      (bv_to_little_endian (Z.of_nat count) 8 (z / 256)).
    rewrite IH.
    + rewrite Z.mod_eq by lia. lia.
    + split.
      * apply Z.div_pos; lia.
      * rewrite Nat2Z.inj_succ in Hz.
        replace (8 * (Z.of_nat count + 1)) with
            (8 * Z.of_nat count + 8) in Hz by lia.
        rewrite Z.pow_add_r in Hz by lia.
        change (2 ^ 8) with 256 in Hz.
        apply Z.div_lt_upper_bound; lia.
Qed.

Lemma decodeItemSavedFrameFacts_two_words
    (args : DecodeItemArgs) (saved returnBytes : list byte) :
  length saved = 8%nat ->
  length returnBytes = 8%nat ->
  littleEndian saved = bv_unsigned (decodeItemSavedFramePointer args) ->
  littleEndian returnBytes = decodeItemReturnAddress args ->
  decodeItemSavedFrameFacts args (saved ++ returnBytes).
Proof.
  intros Hsaved Hreturn HsavedValue HreturnValue.
  unfold decodeItemSavedFrameFacts, word64At.
  rewrite app_length, Hsaved, Hreturn.
  split; [lia|].
  split.
  - rewrite skipn_O, firstn_app, Hsaved. simpl.
    rewrite firstn_all2 by lia. rewrite app_nil_r.
    split; assumption.
  - rewrite skipn_app, Hsaved. simpl.
    rewrite skipn_all2 by lia. simpl.
    rewrite skipn_O, firstn_all2 by lia.
    split; assumption.
Qed.

Print Assumptions decodeItemSavedFrameFacts_two_words.

Lemma decodeItemSavedFrameFacts_machine_words (args : DecodeItemArgs) :
  decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args
    (bv_to_little_endian 8 8
       (bv_unsigned (decodeItemSavedFramePointer args)) ++
     bv_to_little_endian 8 8
       (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args)))).
Proof.
  intros Hdomain.
  assert (Hreturn :
      0 <= decodeItemReturnAddress args < word64Modulus).
  { unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hdomain.
    destruct Hdomain as (_ & _ & Hlayout).
    unfold decodeItemEntryLayout in Hlayout. tauto. }
  apply decodeItemSavedFrameFacts_two_words.
  - rewrite length_bv_to_little_endian; lia.
  - rewrite length_bv_to_little_endian; lia.
  - apply (littleEndian_machine_bytes 8%nat).
    change (8 * Z.of_nat 8) with 64.
    pose proof (bv_unsigned_in_range 64 (decodeItemSavedFramePointer args)).
    unfold bv_modulus in H. exact H.
  - rewrite (littleEndian_machine_bytes 8%nat).
    + rewrite Z_to_bv_small; [reflexivity|].
      unfold bv_modulus, word64Modulus in Hreturn. exact Hreturn.
    + change (8 * Z.of_nat 8) with 64.
      pose proof (bv_unsigned_in_range 64
        (Z_to_bv 64 (decodeItemReturnAddress args))).
      unfold bv_modulus in H. exact H.
Qed.

Print Assumptions littleEndian_machine_bytes.
Print Assumptions decodeItemSavedFrameFacts_machine_words.

Global Instance decodeItemSavedFrameFacts_derived
    (returnAddress : Z) (args : DecodeItemArgs)
    `{!ZesuStepWordArrayHandoff} :
  ZesuDerivedFacts
    (decodeItemDomainAt returnAddress decodeItemC1BDomain args)
    (decodeItemSavedFrameFacts args
      (bv_to_little_endian 8 8
         (bv_unsigned (decodeItemSavedFramePointer args)) ++
       bv_to_little_endian 8 8
         (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args))))).
Proof.
  intros [_ Hdomain].
  exact (decodeItemSavedFrameFacts_machine_words args Hdomain).
Qed.
