From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefix15694PositionStates args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPositionState remaining 0 state /\
  writeSuccessWithdrawalsPositionState remaining 1
    (writeSuccessWithdrawalsPrefixState98 state.1 sp, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 2
    (writeSuccessWithdrawalsPrefixState9c state.1 sp, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 3
    (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 4
    (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer, priorLog).
Proof.
  intros Hinv.
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  have Hpc : state.1.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15694)).
  { destruct (writeSuccessWithdrawalsInv15694DirectEntry args sp pointer base
      total processed (S remaining) withdrawal allBytes prefix current suffix
      scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as
      (? & ? & ? & ? & _ & Hpc & _). exact Hpc. }
  have HstatePc : writeSuccessWithdrawalsConcretePc state = Some 0x15694 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx9_98 :
      (writeSuccessWithdrawalsPrefixState98 state.1 sp).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local. cbn. rewrite writeSuccess15694RegsLookupOther;
      try discriminate. exact Hx9. }
  have Hx9_9c :
      (writeSuccessWithdrawalsPrefixState9c state.1 sp).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsPrefixState9c, writeSuccess15698After,
      writeSuccess15694Local. cbn. rewrite writeSuccess15698RegsLookupOther;
      try discriminate. exact Hx9_98. }
  have Hx9_a0 :
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsPrefixStatea0, writeSuccess1569cAfter,
      writeSuccess1569cLocal. cbn. rewrite writeSuccess1569cRegsLookupOther;
      try discriminate. exact Hx9_9c. }
  have Hx9_a4 :
      (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsPrefixStatea4, writeSuccess156a0After,
      writeSuccess15694Local. cbn. rewrite writeSuccess156a0RegsLookupOther;
      try discriminate. exact Hx9_a0. }
  repeat split.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 0 state
      0x15694).
    + lia.
    + reflexivity.
    + exact HstatePc.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 1
      (writeSuccessWithdrawalsPrefixState98 state.1 sp, priorLog) 0x15698).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess15694NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9_98.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 2
      (writeSuccessWithdrawalsPrefixState9c state.1 sp, priorLog) 0x1569c).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccessWithdrawalsPrefixState9c, writeSuccess15698After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess15698NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9_9c.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 3
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog)
      0x156a0).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccessWithdrawalsPrefixStatea0, writeSuccess1569cAfter,
        writeSuccess1569cLocal. cbn. rewrite lookup_insert.
      rewrite writeSuccess1569cNextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9_a0.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 4
      (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer, priorLog)
      0x156a4).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccessWithdrawalsPrefixStatea4, writeSuccess156a0After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess156a0NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9_a4.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694PositionStates.
