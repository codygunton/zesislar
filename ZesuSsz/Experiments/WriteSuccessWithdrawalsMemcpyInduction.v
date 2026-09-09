From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessMemcpyByteReady (regs : reg_map) (global : seq_global_state)
    (source destination index length : bv 64) (byte : bv 8) : Prop :=
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) /\
  regs !! "x10" = Some (RVal_Bits destination) /\
  regs !! "x11" = Some (RVal_Bits source) /\
  regs !! "x12" = Some (RVal_Bits length) /\
  regs !! "x15" = Some (RVal_Bits index) /\
  index <> length /\
  writeSuccessWithdrawalsInstructionTable global /\
  writeSuccessWithdrawalsOperationalRegisterFacts regs /\
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccessMemcpySourceAddress source index)) 1 =
    Some (bv_to_bvn byte) /\
  0x20000000 <= bv_unsigned (writeSuccessMemcpySourceAddress source index) /\
  bv_unsigned (writeSuccessMemcpySourceAddress source index) + 1 <= 0x40000000 /\
  0x20000000 <= bv_unsigned
    (writeSuccessMemcpyDestinationAddress destination index) /\
  bv_unsigned (writeSuccessMemcpyDestinationAddress destination index) + 1 <=
    0x40000000 /\
  is_Some (global.(seq_mem) !!
    writeSuccessMemcpyDestinationAddress destination index).

Fixpoint writeSuccessMemcpyBytesReady (regs : reg_map)
    (global : seq_global_state) (source destination index length : bv 64)
    (bytes : list (bv 8)) : Prop :=
  match bytes with
  | [] => True
  | byte :: tail =>
      writeSuccessMemcpyByteReady regs global source destination index length byte /\
      writeSuccessMemcpyBytesReady
        (writeSuccessMemcpyByteRegs regs source destination index byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination index)
          (writeSuccess101e4Loaded byte))
        source destination (index + BV 64 1)%bv length tail
  end.

Fixpoint writeSuccessMemcpyBytesAfter (regs : reg_map)
    (global : seq_global_state) (source destination index : bv 64)
    (bytes : list (bv 8)) : IslaState :=
  match bytes with
  | [] => writeSuccess101d8Before regs global
  | byte :: tail =>
      writeSuccessMemcpyBytesAfter
        (writeSuccessMemcpyByteRegs regs source destination index byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination index)
          (writeSuccess101e4Loaded byte))
        source destination (index + BV 64 1)%bv tail
  end.

Theorem writeSuccessMemcpyBytesRun (regs : reg_map) (global : seq_global_state)
    (source destination index totalLength : bv 64) (bytes : list (bv 8)) :
  writeSuccessMemcpyBytesReady regs global source destination index totalLength bytes ->
  exists segments,
    IslaInstructionRun (7 * List.length bytes)
      (writeSuccess101d8Before regs global) segments
      (writeSuccessMemcpyBytesAfter regs global source destination index bytes).
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index Hready.
  - exists []. cbn. constructor.
  - cbn in Hready |- *. destruct Hready as [Hhead Htail].
    unfold writeSuccessMemcpyByteReady in Hhead.
    destruct Hhead as
      (Hpc & Hx10 & Hx11 & Hx12 & Hx15 & Hne & Htable & Hfacts & Hread &
       HsourceLower & HsourceUpper & HdestinationLower & HdestinationUpper &
       Hbacked).
    destruct (writeSuccessMemcpyByteRun regs global source destination index
      totalLength byte Hpc Hx10 Hx11 Hx12 Hx15 Hne Htable Hfacts Hread
      HsourceLower HsourceUpper HdestinationLower HdestinationUpper Hbacked) as
      (headSegments & HheadRun).
    destruct (IH
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv Htail) as (tailSegments & HtailRun).
    exists (headSegments ++ tailSegments).
    replace (7 * S (List.length tail))%nat with (7 + 7 * List.length tail)%nat by lia.
    eapply islaInstructionRun_app; first exact HheadRun.
    exact HtailRun.
Qed.

Print Assumptions writeSuccessMemcpyBytesRun.
