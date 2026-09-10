From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBytePositionPath.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBytePositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessMemcpyBytePositionPrefixState remaining byteIndex regs global
    (source destination index length : bv 64) byte priorLog offset state :
  index = Z_to_bv 64 (Z.of_nat byteIndex) ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits index) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  (byteIndex < 48)%nat ->
  (offset < 7)%nat ->
  nth_error (writeSuccessMemcpyBytePositionPrefixStates regs global source
    destination index length byte priorLog) offset = Some state ->
  writeSuccessWithdrawalsPositionState remaining
    (6 + 7 * byteIndex + offset) state.
Proof.
  intros Hindex Hpc Hx15 Hx9 Hrange Hbyte Hoffset Hstate.
  eapply writeSuccessWithdrawalsMemcpyLoopPositionState;
    [exact Hbyte|exact Hoffset| | | |exact Hrange].
  - destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia;
      cbn [writeSuccessMemcpyBytePositionPrefixStates] in Hstate;
      injection Hstate as <-;
      cbn [writeSuccessWithdrawalsMemcpyBytePcs nth];
      unfold writeSuccessWithdrawalsConcretePc; cbn;
    unfold writeSuccessMemcpyByteState1, writeSuccessMemcpyByteState2,
      writeSuccessMemcpyByteState3, writeSuccessMemcpyByteState4,
      writeSuccessMemcpyByteState5, writeSuccessMemcpyByteState6,
      writeSuccessMemcpyByteRegs1, writeSuccessMemcpyByteRegs2,
      writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs4,
      writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs6;
      cbn; try (rewrite Hpc; reflexivity);
      repeat rewrite lookup_insert; reflexivity.
  - destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia;
      cbn [writeSuccessMemcpyBytePositionPrefixStates] in Hstate;
      injection Hstate as <-;
      cbn;
      unfold writeSuccessMemcpyByteState1, writeSuccessMemcpyByteState2,
      writeSuccessMemcpyByteState3, writeSuccessMemcpyByteState4,
      writeSuccessMemcpyByteState5, writeSuccessMemcpyByteState6,
      writeSuccessMemcpyByteRegs1, writeSuccessMemcpyByteRegs2,
      writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs4,
      writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs6;
      cbn; repeat (rewrite lookup_insert_ne; last discriminate).
    all: try rewrite Hx15.
    all: try rewrite lookup_insert.
    all: rewrite Hindex.
    all: repeat f_equal; apply bv_eq; bv_solve.
  - destruct offset as [|[|[|[|[|[|[|offset]]]]]]]; try lia;
      cbn [writeSuccessMemcpyBytePositionPrefixStates] in Hstate;
      injection Hstate as <-;
      unfold writeSuccessMemcpyByteState1, writeSuccessMemcpyByteState2,
      writeSuccessMemcpyByteState3, writeSuccessMemcpyByteState4,
      writeSuccessMemcpyByteState5, writeSuccessMemcpyByteState6,
      writeSuccessMemcpyByteRegs1, writeSuccessMemcpyByteRegs2,
      writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs4,
      writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs6;
      cbn; repeat (rewrite lookup_insert_ne; last discriminate).
    all: exact Hx9.
Qed.

Theorem writeSuccessMemcpyBytesPositionStatesAll remaining startIndex regs global
    (source destination index length : bv 64) bytes priorLog offset state :
  index = Z_to_bv 64 (Z.of_nat startIndex) ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits index) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  (startIndex + List.length bytes <= 48)%nat ->
  (offset < 7 * List.length bytes)%nat ->
  nth_error (writeSuccessMemcpyBytesPositionStates regs global source
    destination index length bytes priorLog) offset = Some state ->
  writeSuccessWithdrawalsPositionState remaining
    (6 + 7 * startIndex + offset) state.
Proof.
  revert startIndex regs global index offset state.
  induction bytes as [|byte tail IH]; intros startIndex regs global index offset
    state Hindex Hpc Hx15 Hx9 Hrange Hlength Hoffset Hstate;
    first (cbn in Hoffset; lia).
  cbn [writeSuccessMemcpyBytesPositionStates] in Hstate.
  destruct (Nat.lt_ge_cases offset 7) as [Hhead|Htail].
  - apply writeSuccessMemcpyBytePositionPrefixState with
      (regs := regs) (global := global) (source := source)
      (destination := destination) (index := index) (length := length)
      (byte := byte) (priorLog := priorLog) (offset := offset);
      try assumption.
    + lia.
    + rewrite nth_error_app1 in Hstate; [exact Hstate|cbn; lia].
  - have HnextIndex : (index + BV 64 1)%bv =
        Z_to_bv 64 (Z.of_nat (S startIndex)).
    { rewrite Hindex. apply bv_eq. bv_solve. }
    have HnextX15 :
        writeSuccessMemcpyByteRegs regs source destination index byte !! "x15" =
        Some (RVal_Bits (index + BV 64 1)%bv) :=
      writeSuccessMemcpyByteRegsX15 regs source destination index byte.
    have HnextX9 :
        writeSuccessMemcpyByteRegs regs source destination index byte !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite writeSuccessMemcpyByteRegsLookupOther; try discriminate.
      exact Hx9. }
    rewrite nth_error_app2 in Hstate; last (cbn; lia).
    cbn in Hstate.
    have Hresult := IH (S startIndex)
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv (offset - 7)%nat state HnextIndex
      (writeSuccessMemcpyByteRegsPc regs source destination index byte)
      HnextX15 HnextX9 Hrange ltac:(cbn in Hlength; lia)
      ltac:(cbn in Hoffset; lia) Hstate.
    replace (6 + 7 * startIndex + offset)%nat with
      (6 + 7 * S startIndex + (offset - 7))%nat by lia.
    exact Hresult.
Qed.

Theorem writeSuccessWithdrawalsMemcpyCanonicalPositionStates remaining regs
    global (source destination : bv 64) bytes priorLog :
  List.length bytes = 48%nat ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  let initRegs := writeSuccess101d4Regs regs in
  let loopAfter := writeSuccessMemcpyBytesAfter initRegs global source
    destination (BV 64 0) bytes in
  (forall offset state,
    (offset < 7 * List.length bytes)%nat ->
    nth_error (writeSuccessMemcpyBytesPositionStates initRegs global source
      destination (BV 64 0) (BV 64 48) bytes priorLog) offset = Some state ->
    writeSuccessWithdrawalsPositionState remaining (6 + offset) state) /\
  writeSuccessWithdrawalsPositionState remaining 342
    (writeSuccess101d8Before loopAfter.1.(seq_regs) loopAfter.2, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 343
    (writeSuccess101d8FallthroughAfter loopAfter.1.(seq_regs) loopAfter.2,
     priorLog).
Proof.
  intros Hlength Hx9 Hrange initRegs loopAfter.
  have HinitPc : initRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101d8)).
  { unfold initRegs, writeSuccess101d4Regs. rewrite lookup_insert.
    rewrite writeSuccess101d4NextPcExact. reflexivity. }
  have HinitX15 : initRegs !! "x15" = Some (RVal_Bits (BV 64 0)).
  { unfold initRegs, writeSuccess101d4Regs.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    reflexivity. }
  have HinitX9 : initRegs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
      try discriminate. exact Hx9. }
  have HloopPc : loopAfter.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101d8)).
  { unfold loopAfter. apply writeSuccessMemcpyBytesAfterPc. exact HinitPc. }
  have HloopX15 : loopAfter.1.(seq_regs) !! "x15" =
      Some (RVal_Bits (Z_to_bv 64 48)).
  { unfold loopAfter.
    rewrite (writeSuccessMemcpyBytesAfterX15 initRegs global source destination
      (BV 64 0) bytes HinitX15). rewrite Hlength.
    all: try reflexivity.
    all: try (apply bv_eq; bv_solve).
  }
  have HloopX9 : loopAfter.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold loopAfter. rewrite writeSuccessMemcpyBytesAfterLookupOther;
      try discriminate. exact HinitX9. }
  split.
  - intros offset state Hoffset Hstate.
    replace (6 + offset)%nat with (6 + 7 * 0 + offset)%nat by lia.
    eapply writeSuccessMemcpyBytesPositionStatesAll with
      (startIndex := 0%nat) (regs := initRegs) (global := global)
      (source := source) (destination := destination) (index := BV 64 0)
      (length := BV 64 48) (bytes := bytes) (priorLog := priorLog);
      try eassumption.
    + apply bv_eq. bv_solve.
    + rewrite Hlength. lia.
  - split.
    + eapply writeSuccessWithdrawalsMemcpyExitPositionState.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess101d8Before,
          writeSuccess15694Local. cbn. rewrite HloopPc.
        unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned.
        vm_compute. reflexivity.
      * exact HloopX15.
      * exact HloopX9.
      * exact Hrange.
    + eapply writeSuccessWithdrawalsMemcpyReturnPositionState.
      * unfold writeSuccessWithdrawalsConcretePc,
          writeSuccess101d8FallthroughAfter,
          writeSuccess101d8FallthroughRegs, writeSuccess15694Local. cbn.
        rewrite lookup_insert. unfold bvn_unsigned. cbn.
        rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
      * unfold writeSuccess101d8FallthroughAfter,
          writeSuccess101d8FallthroughRegs, writeSuccess15694Local. cbn.
        rewrite lookup_insert_ne; last discriminate. exact HloopX9.
      * exact Hrange.
Qed.

Print Assumptions writeSuccessMemcpyBytePositionPrefixState.
Print Assumptions writeSuccessMemcpyBytesPositionStatesAll.
Print Assumptions writeSuccessWithdrawalsMemcpyCanonicalPositionStates.
