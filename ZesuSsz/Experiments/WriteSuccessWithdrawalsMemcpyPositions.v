From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessInstructionRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBytePositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBytePositionPath.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.

Import ListNotations.

Definition writeSuccessMemcpyBytePositionPrefixStates (regs : reg_map)
    (global : seq_global_state) (source destination index length : bv 64)
    (byte : bv 8) (priorLog : list WriteSuccessWithdrawalsRecord) :
    list WriteSuccessWithdrawalsConcreteState :=
  [(writeSuccess101d8Before regs global, priorLog);
   (writeSuccessMemcpyByteState1 regs global, priorLog);
   (writeSuccessMemcpyByteState2 regs global source index, priorLog);
   (writeSuccessMemcpyByteState3 regs global source index byte, priorLog);
   (writeSuccessMemcpyByteState4 regs global source destination index byte,
    priorLog);
   (writeSuccessMemcpyByteState5 regs global source destination index byte,
    priorLog);
   (writeSuccessMemcpyByteState6 regs global source destination index byte,
    priorLog)].

Fixpoint writeSuccessMemcpyBytesPositionStates (regs : reg_map)
    (global : seq_global_state) (source destination index length : bv 64)
    (bytes : list (bv 8)) (priorLog : list WriteSuccessWithdrawalsRecord) :
    list WriteSuccessWithdrawalsConcreteState :=
  match bytes with
  | [] => [(writeSuccess101d8Before regs global, priorLog)]
  | byte :: tail =>
      writeSuccessMemcpyBytePositionPrefixStates regs global source destination
        index length byte priorLog ++
      writeSuccessMemcpyBytesPositionStates
        (writeSuccessMemcpyByteRegs regs source destination index byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination index)
          (writeSuccess101e4Loaded byte))
        source destination (index + BV 64 1)%bv length tail priorLog
  end.

Lemma writeSuccessMemcpyBytePositionStatesSplit regs global source destination
    index length byte priorLog :
  writeSuccessMemcpyBytePositionStates regs global source destination index
      length byte priorLog =
    writeSuccessMemcpyBytePositionPrefixStates regs global source destination
      index length byte priorLog ++
    [(writeSuccessMemcpyByteAfter regs global source destination index byte,
      priorLog)].
Proof. reflexivity. Qed.

Lemma writeSuccessMemcpyBytesPositionStatesHead regs global source destination
    index length bytes priorLog :
  writeSuccessMemcpyBytesPositionStates regs global source destination index
      length bytes priorLog =
    (writeSuccess101d8Before regs global, priorLog) ::
      tl (writeSuccessMemcpyBytesPositionStates regs global source destination
        index length bytes priorLog).
Proof. destruct bytes; reflexivity. Qed.

Theorem writeSuccessMemcpyBytesPositionPath (regs : reg_map)
    (global : seq_global_state) (source destination index length : bv 64)
    (bytes : list (bv 8)) priorLog segments after :
  writeSuccessMemcpyBytesReady regs global source destination index length bytes ->
  IslaInstructionRun (7 * List.length bytes)
    (writeSuccess101d8Before regs global) segments after ->
  after = writeSuccessMemcpyBytesAfter regs global source destination index bytes /\
  WriteSuccessWithdrawalsPositionEdges segments
    (writeSuccessMemcpyBytesPositionStates regs global source destination index
      length bytes priorLog).
Proof.
  revert regs global index segments after.
  induction bytes as [|byte tail IH]; intros regs global index segments after
    Hready Hrun.
  - cbn in Hrun |- *. inversion Hrun; subst. split; reflexivity.
  - cbn in Hready |- *. destruct Hready as (HheadReady & HtailReady).
    replace (7 * S (List.length tail))%nat with
      (7 + 7 * List.length tail)%nat in Hrun by lia.
    destruct (islaInstructionRun_split 7 (7 * List.length tail) _ _ _ Hrun) as
      (headSegments & middle & tailSegments & Hsegments & HheadRun & HtailRun).
    destruct (writeSuccessMemcpyBytePositionPath regs global source destination
      index length byte priorLog headSegments middle HheadReady HheadRun) as
      (Hmiddle & HheadEdges).
    subst middle.
    destruct (IH
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv tailSegments after HtailReady HtailRun) as
      (Hafter & HtailEdges).
    split; first exact Hafter.
    subst segments.
    rewrite writeSuccessMemcpyBytePositionStatesSplit in HheadEdges.
    rewrite (writeSuccessMemcpyBytesPositionStatesHead
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte)) source destination
      (index + BV 64 1)%bv length tail priorLog) in HtailEdges.
    have Hboundary :
        writeSuccessMemcpyByteAfter regs global source destination index byte =
        writeSuccess101d8Before
          (writeSuccessMemcpyByteRegs regs source destination index byte)
          (writeSuccess101f0Global global
            (writeSuccessMemcpyDestinationAddress destination index)
            (writeSuccess101e4Loaded byte)) by reflexivity.
    rewrite <- Hboundary in HtailEdges.
    rewrite (writeSuccessMemcpyBytesPositionStatesHead
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte)) source destination
      (index + BV 64 1)%bv length tail priorLog).
    rewrite <- Hboundary.
    eapply (writeSuccessWithdrawalsPositionEdgesApp headSegments
      (writeSuccessMemcpyBytePositionPrefixStates regs global source destination
        index length byte priorLog)
      (writeSuccessMemcpyByteAfter regs global source destination index byte,
       priorLog)
      tailSegments
      (tl (writeSuccessMemcpyBytesPositionStates
        (writeSuccessMemcpyByteRegs regs source destination index byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination index)
          (writeSuccess101e4Loaded byte)) source destination
        (index + BV 64 1)%bv length tail priorLog)));
      eassumption.
Qed.

Print Assumptions writeSuccessMemcpyBytePositionStatesSplit.
Print Assumptions writeSuccessMemcpyBytesPositionStatesHead.
Print Assumptions writeSuccessMemcpyBytesPositionPath.
