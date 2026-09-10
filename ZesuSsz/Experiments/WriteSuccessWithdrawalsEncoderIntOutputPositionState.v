From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Import ListNotations.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderOutputSavedReturn state
    (sp returnAddress : bv 64) :
  state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits (sp - BV 64 16)%bv) ->
  read_mem state.1.2.(seq_mem) (bv_unsigned sp - 8) 8%N =
    Some (bv_to_bvn returnAddress) ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  writeSuccessWithdrawalsSavedReturn state = Some (bv_unsigned returnAddress).
Proof.
  intros Hx2 Hread Hrange.
  unfold writeSuccessWithdrawalsSavedReturn,
    writeSuccessWithdrawalsRegisterUnsigned. cbn. rewrite Hx2.
  unfold bvn_unsigned. rewrite (writeSuccessEncoderIntStackUnsigned sp Hrange).
  replace (bv_unsigned sp - 16 + 8) with (bv_unsigned sp - 8) by lia.
  rewrite Hread. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntOutputActualPositions remaining start
    (regs : reg_map) (global : seq_global_state)
    (data size sp returnAddress : bv 64) (returnTrace : isla_trace)
    priorLog segments after :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  regs !! "x2" = Some (RVal_Bits (sp - BV 64 16)%bv) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  read_mem global.(seq_mem) (bv_unsigned sp - 8) 8%N =
    Some (bv_to_bvn returnAddress) ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  global.(seq_instrs) !! writeSuccess15d28Link = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  WriteSuccessWithdrawalsRecordedRun 5
    (writeSuccess10190Before regs global, priorLog) segments after ->
  exists states,
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 5)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (7 + offset))%nat stateAt.
Proof.
  intros Hstart Hpc Hx1 Hx2 Hx10 Hx11 Hx9 Hcounter Hread Hrange
    Hreturn Htable Hfacts Hdom Hrecorded.
  have HlinkAlign : bv_extract 0 2 writeSuccess15d28Link = BV 2 0.
  { apply bv_eq. native_compute. reflexivity. }
  destruct (writeSuccessOutputRecordedPositionPath regs global data size
    writeSuccess15d28Link returnTrace priorLog segments after Hpc Hx1 Hx10 Hx11
    HlinkAlign Hreturn Htable Hfacts Hdom Hrecorded) as
    (mstatus & satp & result98 & result9c & states & Hsegments & Hafter &
     Hlength & Hstate0 & Hstate5 & Hedges).
  exists states. split; first exact Hedges.
  intros offset stateAt Hoffset Hstate.
  destruct offset as [|offset].
  - rewrite Hstate0 in Hstate. injection Hstate as <-.
    eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
      (returnAddress := returnAddress) (offset := 7%nat) (pc := 0x10190).
    + exact Hstart.
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess10190Before.
      cbn. rewrite Hpc. reflexivity.
    + apply writeSuccessWithdrawalsEncoderOutputSelected.
      * cbn; tauto.
      * exact Hx1.
      * eapply writeSuccessWithdrawalsEncoderOutputSavedReturn; eassumption.
    + exact Hx9.
    + exact Hcounter.
  - destruct offset as [|offset].
    + have Hobs : nth_error segments 0 =
        Some (writeSuccess10190Observations regs global).
      { rewrite Hsegments. reflexivity. }
      destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 0
        _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
        Hedges Hobs Hstate) as (labels & Hlast).
      have Hmachine := f_equal microAfter Hlast.
      cbn [writeSuccess10190Observations writeSuccess10190PrefixObservations]
        in Hmachine.
      destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
      eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
        (returnAddress := returnAddress) (offset := 8%nat) (pc := 0x10194).
      * exact Hstart.
      * lia.
      * reflexivity.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess10190After.
        cbn. rewrite lookup_insert. reflexivity.
      * apply writeSuccessWithdrawalsEncoderOutputSelected.
        -- cbn; tauto.
        -- unfold writeSuccessOutputRegs1.
           rewrite writeSuccess10190RegsLookupOther; try discriminate. exact Hx1.
        -- eapply writeSuccessWithdrawalsEncoderOutputSavedReturn.
           ++ unfold writeSuccessOutputRegs1.
              rewrite writeSuccess10190RegsLookupOther; try discriminate. exact Hx2.
           ++ exact Hread.
           ++ exact Hrange.
      * unfold writeSuccessOutputRegs1.
        rewrite writeSuccess10190RegsLookupOther; try discriminate. exact Hx9.
      * exact Hcounter.
    + destruct offset as [|offset].
      * have Hobs : nth_error segments 1 = Some
          (writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
            writeSuccess10190Link).
        { rewrite Hsegments. reflexivity. }
        destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 1
          _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
          Hedges Hobs Hstate) as (labels & Hlast).
        have Hmachine := f_equal microAfter Hlast.
        cbn [writeSuccess10194Observations writeSuccess10194PrefixObservations]
          in Hmachine.
        destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
        eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
          (returnAddress := returnAddress) (offset := 9%nat) (pc := 0x10198).
        -- exact Hstart.
        -- lia.
        -- reflexivity.
        -- unfold writeSuccessWithdrawalsConcretePc, writeSuccess10194After.
           cbn. rewrite lookup_insert. reflexivity.
        -- apply writeSuccessWithdrawalsEncoderOutputSelected.
           ++ cbn; tauto.
           ++ rewrite writeSuccessOutputRegs2LookupOther; try discriminate. exact Hx1.
           ++ eapply writeSuccessWithdrawalsEncoderOutputSavedReturn.
              ** rewrite writeSuccessOutputRegs2LookupOther; try discriminate. exact Hx2.
              ** exact Hread.
              ** exact Hrange.
        -- rewrite writeSuccessOutputRegs2LookupOther; try discriminate. exact Hx9.
        -- exact Hcounter.
      * destruct offset as [|offset].
        -- have Hobs : nth_error segments 2 = Some
             (writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
               mstatus writeSuccessOutputPortBase satp data result98
               WriteSuccessStoreMmio).
           { rewrite Hsegments. reflexivity. }
           destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 2
             _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
             Hedges Hobs Hstate) as (labels & Hlast).
           have Hmachine := f_equal microAfter Hlast.
           cbn [writeSuccess10198Observations writeSuccess10198PrefixObservations]
             in Hmachine.
           destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
           eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
             (returnAddress := returnAddress) (offset := 10%nat) (pc := 0x1019c).
           ++ exact Hstart.
           ++ lia.
           ++ reflexivity.
           ++ unfold writeSuccessWithdrawalsConcretePc, writeSuccess10198After.
              cbn. rewrite lookup_insert. reflexivity.
           ++ apply writeSuccessWithdrawalsEncoderOutputSelected.
              ** cbn; tauto.
              ** rewrite writeSuccessOutputRegs3LookupOther; try discriminate. exact Hx1.
              ** eapply writeSuccessWithdrawalsEncoderOutputSavedReturn.
                 --- rewrite writeSuccessOutputRegs3LookupOther; try discriminate.
                     exact Hx2.
                 --- exact Hread.
                 --- exact Hrange.
           ++ rewrite writeSuccessOutputRegs3LookupOther; try discriminate. exact Hx9.
           ++ exact Hcounter.
        -- destruct offset as [|offset].
           ++ have Hobs : nth_error segments 3 = Some
                (writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
                  mstatus writeSuccessOutputPortBase satp size result9c
                  WriteSuccessStoreMmio).
              { rewrite Hsegments. reflexivity. }
              destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 3
                _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
                Hedges Hobs Hstate) as (labels & Hlast).
              have Hmachine := f_equal microAfter Hlast.
              cbn [writeSuccess1019cObservations writeSuccess1019cPrefixObservations]
                in Hmachine.
              destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
              eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
                (returnAddress := returnAddress) (offset := 11%nat)
                (pc := 0x101a0).
              ** exact Hstart.
              ** lia.
              ** reflexivity.
              ** unfold writeSuccessWithdrawalsConcretePc, writeSuccess1019cAfter.
                 cbn. rewrite lookup_insert. reflexivity.
              ** apply writeSuccessWithdrawalsEncoderOutputSelected.
                 --- cbn; tauto.
                 --- rewrite writeSuccessOutputRegs4LookupOther; try discriminate.
                     exact Hx1.
                 --- eapply writeSuccessWithdrawalsEncoderOutputSavedReturn.
                     +++ rewrite writeSuccessOutputRegs4LookupOther; try discriminate.
                         exact Hx2.
                     +++ exact Hread.
                     +++ exact Hrange.
              ** rewrite writeSuccessOutputRegs4LookupOther; try discriminate. exact Hx9.
              ** exact Hcounter.
           ++ lia.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderOutputSavedReturn.
Print Assumptions writeSuccessWithdrawalsEncoderIntOutputActualPositions.
