From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessOccurrenceRemainingBound pc occurrence pcs :
  (writeSuccessWithdrawalsOccurrenceRemaining pc occurrence pcs <=
    length pcs)%nat.
Proof.
  revert occurrence. induction pcs as [|candidate pcs IH]; intros occurrence;
    first reflexivity.
  cbn. destruct (Z.eqb pc candidate).
  - destruct occurrence; first reflexivity. specialize (IH occurrence). lia.
  - specialize (IH occurrence). lia.
Qed.

Lemma writeSuccessOccurrenceAtIndexUnique pcs position pc occurrence :
  nth_error pcs position = Some pc ->
  writeSuccessWithdrawalsOccurrenceRemaining pc occurrence pcs =
    (length pcs - position)%nat ->
  occurrence = count_occ Z.eq_dec (firstn position pcs) pc.
Proof.
  revert position occurrence.
  induction pcs as [|candidate pcs IH]; intros position occurrence Hnth Hremain.
  { destruct position; discriminate. }
  destruct position as [|position].
  - cbn in Hnth. injection Hnth as ->.
    destruct occurrence as [|occurrence]; first reflexivity.
    cbn in Hremain. rewrite Z.eqb_refl in Hremain.
    pose proof (writeSuccessOccurrenceRemainingBound pc occurrence pcs).
    lia.
  - cbn in Hnth. cbn [firstn count_occ].
    destruct (Z.eq_dec candidate pc) as [->|Hne].
    + destruct occurrence as [|occurrence].
      * cbn in Hremain. rewrite Z.eqb_refl in Hremain. lia.
      * cbn in Hremain. rewrite Z.eqb_refl in Hremain.
        f_equal. eapply IH; eassumption.
    + have Heqb : Z.eqb pc candidate = false by
        (apply Z.eqb_neq; congruence).
      cbn in Hremain. rewrite Heqb in Hremain.
      eapply IH; eassumption.
Qed.

Lemma writeSuccessWithdrawalsConcatRepeatNth {A : Type} (block : list A)
    count index offset width :
  length block = width ->
  (index < count)%nat ->
  (offset < width)%nat ->
  nth_error (concat (repeat block count)) (width * index + offset) =
    nth_error block offset.
Proof.
  revert index. induction count as [|count IH]; intros index Hlength Hindex Hoffset;
    first lia.
  destruct index as [|index].
  - cbn. replace (width * 0 + offset)%nat with offset by lia.
    rewrite nth_error_app1; first reflexivity.
    rewrite Hlength. lia.
  - cbn. rewrite nth_error_app2; last (rewrite Hlength; lia).
    rewrite Hlength.
    replace (width * S index + offset - width)%nat with
      (width * index + offset)%nat by lia.
    eapply IH; [exact Hlength|lia|exact Hoffset].
Qed.

Lemma writeSuccessWithdrawalsMemcpyLoopPc position offset :
  (position < 48)%nat ->
  (offset < 7)%nat ->
  nth_error writeSuccessWithdrawalsIterationPcs (6 + 7 * position + offset) =
    nth_error writeSuccessWithdrawalsMemcpyBytePcs offset.
Proof.
  intros Hposition Hoffset.
  rewrite writeSuccessWithdrawalsIterationPcsMemcpyLayout.
  rewrite nth_error_app2; last (cbn; lia).
  replace (6 + 7 * position + offset - 6)%nat with
    (7 * position + offset)%nat by lia.
  rewrite nth_error_app1.
  - apply writeSuccessWithdrawalsConcatRepeatNth with (width := 7%nat);
      try assumption. reflexivity.
  - rewrite writeSuccessWithdrawalsMemcpyRepeatedLength. lia.
Qed.

Theorem writeSuccessWithdrawalsMemcpyLoopPositionState remaining byteIndex
    offset state :
  (byteIndex < 48)%nat ->
  (offset < 7)%nat ->
  let pc := nth offset writeSuccessWithdrawalsMemcpyBytePcs 0 in
  let registerIndex := if (offset <? 5)%nat then byteIndex else S byteIndex in
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat registerIndex))) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining
    (6 + 7 * byteIndex + offset) state.
Proof.
  intros Hbyte Hoffset pc registerIndex Hpc Hx15 Hx9 Hrange.
  have Hlocal : nth_error writeSuccessWithdrawalsMemcpyBytePcs offset = Some pc.
  { destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia; reflexivity. }
  have Hnth := writeSuccessWithdrawalsMemcpyLoopPc byteIndex offset Hbyte Hoffset.
  rewrite Hlocal in Hnth.
  exists pc. split; first exact Hnth.
  split; first exact Hpc.
  split.
  - have Hselected : writeSuccessWithdrawalsSelectedOccurrence state pc =
        Some byteIndex.
    { destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia;
        cbn [writeSuccessWithdrawalsMemcpyBytePcs nth] in pc, registerIndex,
          Hpc, Hx15 |- *;
        subst pc registerIndex;
        unfold writeSuccessWithdrawalsSelectedOccurrence,
          writeSuccessWithdrawalsRegisterUnsigned;
        rewrite Hx15; unfold bvn_unsigned; cbn;
        rewrite Z_to_bv_unsigned bv_wrap_small; cbn;
        try rewrite Nat2Z.id; try reflexivity;
        unfold bv_modulus; cbn; lia. }
    rewrite Hselected. f_equal.
    eapply writeSuccessOccurrenceAtIndexUnique; first exact Hnth.
    destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia;
      cbn [writeSuccessWithdrawalsMemcpyBytePcs nth] in pc, Hpc, Hlocal |- *;
      subst pc;
      rewrite writeSuccessWithdrawalsIterationPcsLength;
      try (rewrite writeSuccessWithdrawalsOccurrence101d8Formula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101e0Formula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101e4Formula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101e8Formula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101ecFormula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101f0Formula; [lia|lia]);
      try (rewrite writeSuccessWithdrawalsOccurrence101f4Formula; [lia|lia]).
  - split; first exact Hx9.
    destruct (writeSuccessWithdrawalsOrdinaryPosition
      (6 + 7 * byteIndex + offset) pc ltac:(lia) Hnth) as
      (HnotE4 & HnotE8 & Hnot8c & Hnot90).
    repeat split; assumption.
Qed.

Theorem writeSuccessWithdrawalsMemcpyEntryPositionState remaining state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d4 ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining 5 state.
Proof.
  intros Hpc Hx9 Hrange. exists 0x101d4.
  split; first reflexivity. split; first exact Hpc. split.
  - unfold writeSuccessWithdrawalsSelectedOccurrence. reflexivity.
  - split; first exact Hx9.
    destruct (writeSuccessWithdrawalsOrdinaryPosition 5 0x101d4
      ltac:(lia) ltac:(reflexivity)) as (H1 & H2 & H3 & H4).
    repeat split; assumption.
Qed.

Theorem writeSuccessWithdrawalsMemcpyExitPositionState remaining state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 48)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining 342 state.
Proof.
  intros Hpc Hx15 Hx9 Hrange. exists 0x101d8.
  split; first reflexivity. split; first exact Hpc. split.
  - have Hselected : writeSuccessWithdrawalsSelectedOccurrence state 0x101d8 =
        Some 48%nat.
    { unfold writeSuccessWithdrawalsSelectedOccurrence,
        writeSuccessWithdrawalsRegisterUnsigned.
      rewrite Hx15. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned bv_wrap_small; cbn; first reflexivity.
      unfold bv_modulus. cbn. lia. }
    rewrite Hselected. reflexivity.
  - split; first exact Hx9.
    destruct (writeSuccessWithdrawalsOrdinaryPosition 342 0x101d8
      ltac:(lia) ltac:(reflexivity)) as (H1 & H2 & H3 & H4).
    repeat split; assumption.
Qed.

Theorem writeSuccessWithdrawalsMemcpyReturnPositionState remaining state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101dc ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining 343 state.
Proof.
  intros Hpc Hx9 Hrange. exists 0x101dc.
  split; first reflexivity. split; first exact Hpc. split.
  - unfold writeSuccessWithdrawalsSelectedOccurrence. reflexivity.
  - split; first exact Hx9.
    destruct (writeSuccessWithdrawalsOrdinaryPosition 343 0x101dc
      ltac:(lia) ltac:(reflexivity)) as (H1 & H2 & H3 & H4).
    repeat split; assumption.
Qed.

Print Assumptions writeSuccessOccurrenceAtIndexUnique.
Print Assumptions writeSuccessWithdrawalsMemcpyLoopPositionState.
Print Assumptions writeSuccessWithdrawalsMemcpyEntryPositionState.
Print Assumptions writeSuccessWithdrawalsMemcpyExitPositionState.
Print Assumptions writeSuccessWithdrawalsMemcpyReturnPositionState.
