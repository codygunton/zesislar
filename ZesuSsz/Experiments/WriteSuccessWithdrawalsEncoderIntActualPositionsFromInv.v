From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntActualPositions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.

Import ListNotations.

Open Scope Z_scope.

Theorem writeSuccessWithdrawalsEncoderIntActualPositionsFromInv remaining start
    (value sp returnAddress : bv 64) scratch memoryFrame priorLog state
    segments after :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  WriteSuccessWithdrawalsRecordedRun 15 state segments after ->
  exists regs global prefix output suffix prefixStates outputStates suffixStates,
    state.1 = writeSuccess15d10Before regs global /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress value,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         returnAddress value) /\
    segments = (prefix ++ output) ++ suffix /\
    length prefixStates = 8%nat /\
    length outputStates = 6%nat /\
    length suffixStates = 4%nat /\
    nth_error prefixStates 0 = Some state /\
    nth_error prefixStates 7 = nth_error outputStates 0 /\
    nth_error outputStates 5 = nth_error suffixStates 0 /\
    nth_error suffixStates 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges prefix prefixStates /\
    WriteSuccessWithdrawalsPositionEdges output outputStates /\
    WriteSuccessWithdrawalsPositionEdges suffix suffixStates /\
    (forall offset stateAt,
      (offset < 7)%nat ->
      nth_error prefixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt) /\
    (forall offset stateAt,
      (offset < 5)%nat ->
      nth_error outputStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (7 + offset))%nat stateAt) /\
    (forall offset stateAt,
      (offset < 3)%nat ->
      nth_error suffixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (12 + offset))%nat stateAt).
Proof.
  intros Hstart Hinv Hx9 Hcounter Hrecorded.
  have HinvExact := Hinv.
  destruct (block_encoder_int_recorded_covered_exact value sp returnAddress
    scratch memoryFrame priorLog state segments after HinvExact Hrecorded) as
    (regs & global & Hentry & Hafter).
  destruct state as [machine log]. cbn in Hentry, Hx9, Hrecorded, Hinv.
  subst machine.
  unfold Inv_encoder_int in Hinv. cbn in Hinv.
  destruct Hinv as
    (Hboundary & HpcRegister & HconcretePc & Hx1 & Hx2 & Hx10 &
     HreturnAlign & HreturnLookup & HstackAlign & HramLower & HramUpper &
     Hscratch & Hrange & Hbacked & Hframe & Htable & Hfacts & Hmmio & Hlog).
  subst log.
  destruct HreturnLookup as (returnTrace & HreturnTrace).
  have Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)).
  { destruct Hboundary as (Hnb & pc & trace & Hpc & Hsource & Htrace).
    cbn in HpcRegister, Hpc, HconcretePc.
    change (match regs !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x15d10) in HconcretePc.
    rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
    change (bv_unsigned pc = 0x15d10) in Hunsigned.
    have Hpceq : pc = Z_to_bv 64 0x15d10.
    { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
    subst pc. exact Hpc. }
  have Hpositions : exists prefix output suffix prefixStates outputStates
      suffixStates,
      segments = (prefix ++ output) ++ suffix /\
      length prefixStates = 8%nat /\
      length outputStates = 6%nat /\
      length suffixStates = 4%nat /\
      nth_error prefixStates 0 = Some
        (writeSuccess15d10Before regs global, priorLog) /\
      nth_error prefixStates 7 = nth_error outputStates 0 /\
      nth_error outputStates 5 = nth_error suffixStates 0 /\
      nth_error suffixStates 3 = Some after /\
      WriteSuccessWithdrawalsPositionEdges prefix prefixStates /\
      WriteSuccessWithdrawalsPositionEdges output outputStates /\
      WriteSuccessWithdrawalsPositionEdges suffix suffixStates /\
      (forall offset stateAt, (offset < 7)%nat ->
        nth_error prefixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt) /\
      (forall offset stateAt, (offset < 5)%nat ->
        nth_error outputStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (start + (7 + offset))%nat stateAt) /\
      (forall offset stateAt, (offset < 3)%nat ->
        nth_error suffixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (start + (12 + offset))%nat stateAt).
  { eapply writeSuccessWithdrawalsEncoderIntActualPositions with
      (returnTrace := returnTrace) (scratch := scratch)
      (memoryFrame := memoryFrame); eassumption. }
  destruct Hpositions as (prefix & output & suffix & prefixStates &
    outputStates & suffixStates & Hpositions).
  exists regs, global, prefix, output, suffix, prefixStates, outputStates,
    suffixStates.
  split; first reflexivity.
  split; first exact Hafter. exact Hpositions.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntActualPositionsFromInv.
