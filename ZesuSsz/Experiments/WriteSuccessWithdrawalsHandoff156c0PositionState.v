From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0PositionContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156c0HandoffPositionStates args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  let first := writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
    withdrawal in
  let second := writeSuccess156c0After first.1.(seq_regs) first.2 in
  let third := writeSuccess156c4After second.1.(seq_regs) second.2
    (sp + BV 64 1768)%bv in
  let fourth := writeSuccess156c8After third.1.(seq_regs) third.2 in
  forall offset stateAt,
    (offset < 4)%nat ->
    nth_error [(first, priorLog); (second, priorLog); (third, priorLog);
      (fourth, priorLog)] offset = Some stateAt ->
    writeSuccessWithdrawalsPositionState remaining (380 + offset) stateAt.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 first second third fourth.
  destruct (writeSuccessWithdrawals156c0PositionContext args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as
    (HpcReg & Hpc & Hx9first & Hrange).
  cbn in HpcReg, Hpc, Hx9first.
  have Hx9second : second.1.(seq_regs) !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold second, writeSuccess156c0After, writeSuccess15694Local; cbn; rewrite writeSuccess156c0RegsLookupOther; try discriminate; exact Hx9first).
  have Hx9third : third.1.(seq_regs) !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold third, writeSuccess156c4After, writeSuccess15694Local; cbn; rewrite writeSuccess156c4RegsLookupOther; try discriminate; exact Hx9second).
  have Hx9fourth : fourth.1.(seq_regs) !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold fourth, writeSuccess156c8After, writeSuccess15694Local; cbn; rewrite writeSuccess156c8RegsLookupOther; try discriminate; exact Hx9third).
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|[|offset]]]]; try lia; cbn in Hnth; injection Hnth as <-.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 380 (first, priorLog) 0x156c0).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc. cbn. rewrite HpcReg. rewrite Hpc. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + exact Hx9first.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 381 (second, priorLog) 0x156c4).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, second, writeSuccess156c0After, writeSuccess15694Local. cbn. rewrite lookup_insert. rewrite writeSuccess156c0NextPcExact. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + exact Hx9second.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 382 (third, priorLog) 0x156c8).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, third, writeSuccess156c4After, writeSuccess15694Local. cbn. rewrite lookup_insert. rewrite writeSuccess156c4NextPcExact. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + exact Hx9third.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 383 (fourth, priorLog) 0x156cc).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, fourth, writeSuccess156c8After, writeSuccess15694Local. cbn. rewrite lookup_insert. rewrite writeSuccess156c8NextPcExact. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + exact Hx9fourth.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawals156c0HandoffPositionStates.
