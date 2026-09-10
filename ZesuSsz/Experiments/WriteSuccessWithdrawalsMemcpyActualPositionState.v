From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockMemcpyPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositionStates.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessMemcpyBytesAfterAt101d8 regs global source destination index
    bytes :
  writeSuccess101d8Before
    (writeSuccessMemcpyBytesAfter regs global source destination index
      bytes).1.(seq_regs)
    (writeSuccessMemcpyBytesAfter regs global source destination index bytes).2 =
  writeSuccessMemcpyBytesAfter regs global source destination index bytes.
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index; first reflexivity.
  cbn. apply IH.
Qed.

Theorem writeSuccessWithdrawalsMemcpyActualPositionGroups args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 339
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
    segments after ->
  exists regs global returnTrace obsD4 loopSegments obsD8 obsDc,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some returnTrace /\
    after =
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) /\
    segments = [obsD4] ++ loopSegments ++ [obsD8; obsDc] /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) [obsD4]
      (writeSuccess101d4After regs global, priorLog) /\
    WriteSuccessWithdrawalsPositionEdges loopSegments
      (writeSuccessMemcpyBytesPositionStates (writeSuccess101d4Regs regs)
        global pointer (sp + BV 64 1744)%bv (BV 64 0) (BV 64 48)
        current priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyLoopAfter regs global pointer
        (sp + BV 64 1744)%bv current, priorLog) [obsD8]
      (writeSuccess101d8FallthroughAfter
        (writeSuccessMemcpyLoopAfter regs global pointer
          (sp + BV 64 1744)%bv current).1.(seq_regs)
        (writeSuccessMemcpyEndpointGlobal regs global pointer
          (sp + BV 64 1744)%bv current), priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess101d8FallthroughAfter
        (writeSuccessMemcpyLoopAfter regs global pointer
          (sp + BV 64 1744)%bv current).1.(seq_regs)
        (writeSuccessMemcpyEndpointGlobal regs global pointer
          (sp + BV 64 1744)%bv current), priorLog) [obsDc] after /\
    writeSuccessWithdrawalsPositionState remaining 5
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) /\
    (forall offset stateAt,
      (offset < 336)%nat ->
      nth_error (writeSuccessMemcpyBytesPositionStates
        (writeSuccess101d4Regs regs) global pointer (sp + BV 64 1744)%bv
        (BV 64 0) (BV 64 48) current priorLog) offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (6 + offset) stateAt) /\
    writeSuccessWithdrawalsPositionState remaining 342
      (writeSuccessMemcpyLoopAfter regs global pointer
        (sp + BV 64 1744)%bv current, priorLog) /\
    writeSuccessWithdrawalsPositionState remaining 343
      (writeSuccess101d8FallthroughAfter
        (writeSuccessMemcpyLoopAfter regs global pointer
          (sp + BV 64 1744)%bv current).1.(seq_regs)
        (writeSuccessMemcpyEndpointGlobal regs global pointer
          (sp + BV 64 1744)%bv current), priorLog).
Proof.
  intros Hinv Hrecorded.
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  have Hrecorded' : WriteSuccessWithdrawalsRecordedRun (7 * length current + 3)
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
      segments after by (rewrite Hcurrent; exact Hrecorded).
  destruct (writeSuccessWithdrawalsBlockMemcpyPositionGroups
    (sp + BV 64 1744)%bv pointer (Z_to_bv 64 0x156a8) current scratch
    state.1.2.(seq_mem) priorLog
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
    segments after Hmemcpy Hrecorded') as
    (_ & _ & _ & _ & HafterLog & regs & global & returnTrace & Hentry & Hreturn &
     HafterMachine & obsD4 & loopSegments & obsD8 & obsDc & Hsegments & HrD4 &
     Hloop & HrD8 & HrDc).
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  have Hx9start :
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer).1.(seq_regs)
        !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsPrefixAfter,
      writeSuccessWithdrawalsPrefixStatea4,
      writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98. cbn.
    rewrite writeSuccess156a4RegsLookupOther; try discriminate.
    rewrite writeSuccess156a0RegsLookupOther; try discriminate.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate.
    unfold Inv_15694 in Hinv. tauto. }
  have HpcStart : writeSuccessWithdrawalsConcretePc
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) =
      Some 0x101d4.
  { unfold Inv_memcpy in Hmemcpy. cbn in Hmemcpy. tauto. }
  have Hpos5 := writeSuccessWithdrawalsMemcpyEntryPositionState remaining
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) HpcStart
    Hx9start Hrange.
  have HentryRegs := f_equal (fun machine => machine.1.(seq_regs)) Hentry.
  cbn in HentryRegs.
  have Hx9regs : regs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- HentryRegs. exact Hx9start. }
  rewrite Hcurrent in Hloop.
  replace (Z_to_bv 64 0) with (BV 64 0) in Hloop by
    (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat 48)) with (BV 64 48) in Hloop by
    (apply bv_eq; reflexivity).
  destruct (writeSuccessWithdrawalsMemcpyCanonicalPositionStates remaining regs
    global pointer (sp + BV 64 1744)%bv current priorLog Hcurrent Hx9regs Hrange)
    as (HloopPositions & Hexit & HreturnPosition).
  have Htable : writeSuccessWithdrawalsInstructionTable global.
  { unfold Inv_memcpy in Hmemcpy. rewrite Hentry in Hmemcpy. cbn in Hmemcpy.
    tauto. }
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8.
  { apply Htable. cbn. tauto. }
  rewrite Hreturn in Hcode. inversion Hcode. subst returnTrace.
  have HafterExact : after =
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog).
  { destruct after as [afterMachine afterLog].
    cbn in HafterMachine, HafterLog |- *. subst afterMachine afterLog.
    unfold writeSuccessWithdrawals156a8State,
      writeSuccessWithdrawals156a8Regs,
      writeSuccessWithdrawals156a8Global, writeSuccess156a8Before.
    reflexivity. }
  exists regs, global, a156a8, obsD4, loopSegments, obsD8, obsDc.
  split; first exact Hentry.
  split; first exact Hreturn.
  split; first exact HafterExact.
  split; first exact Hsegments.
  split; first exact HrD4.
  split; first exact Hloop.
  split; first exact HrD8.
  split; first exact HrDc.
  split; first exact Hpos5.
  split.
  { intros offset stateAt Hoffset Hnth.
    apply HloopPositions.
    - rewrite Hcurrent. exact Hoffset.
    - exact Hnth. }
  split.
  - unfold writeSuccessMemcpyLoopAfter.
    replace (Z_to_bv 64 0) with (BV 64 0) by
      (apply bv_eq; reflexivity).
    rewrite <- writeSuccessMemcpyBytesAfterAt101d8. exact Hexit.
  - unfold writeSuccessMemcpyEndpointGlobal, writeSuccessMemcpyLoopAfter.
    replace (Z_to_bv 64 0) with (BV 64 0) by
      (apply bv_eq; reflexivity).
    exact HreturnPosition.
Qed.

Print Assumptions writeSuccessWithdrawalsMemcpyActualPositionGroups.
