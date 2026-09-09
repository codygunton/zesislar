From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBoundaryFacts.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Open Scope Z_scope.

Definition writeSuccessWithdrawalsIndexValue
    (withdrawal : WriteSuccessWithdrawalObservation) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal))).

Definition writeSuccessWithdrawals156a8Regs (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8)) :=
  writeSuccessMemcpyEndpointRegs regs global pointer (sp + BV 64 1744)%bv
    current (Z_to_bv 64 0x156a8).

Definition writeSuccessWithdrawals156a8Global (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8)) :=
  writeSuccessMemcpyEndpointGlobal regs global pointer (sp + BV 64 1744)%bv
    current.

Definition writeSuccessWithdrawals156a8State (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8)) :=
  writeSuccess156a8Before
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    (writeSuccessWithdrawals156a8Global regs global sp pointer current).

Definition writeSuccessWithdrawals156acState (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :=
  writeSuccess156a8After
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    (writeSuccessWithdrawals156a8Global regs global sp pointer current)
    (writeSuccessWithdrawalsIndexValue withdrawal).

Definition writeSuccessWithdrawals156b0State (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :=
  writeSuccess156acAfter
    (writeSuccess156a8Regs
      (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      (writeSuccessWithdrawalsIndexValue withdrawal))
    (writeSuccessWithdrawals156a8Global regs global sp pointer current).

Definition writeSuccessWithdrawalsEncoderInt156b4State (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64)
    (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :=
  writeSuccess156b0After
    (writeSuccess156acRegs
      (writeSuccess156a8Regs
        (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
        (writeSuccessWithdrawalsIndexValue withdrawal)))
    (writeSuccessWithdrawals156a8Global regs global sp pointer current).

Lemma writeSuccessWithdrawals156a8Instrs (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8)) :
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) =
    global.(seq_instrs).
Proof.
  unfold writeSuccessWithdrawals156a8Global.
  apply writeSuccessMemcpyEndpointInstrs.
Qed.

Lemma writeSuccessWithdrawals156a8RegsX2 (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8)) :
  regs !! "x2" = Some (RVal_Bits sp) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x2" =
    Some (RVal_Bits sp).
Proof.
  intros Hsp. unfold writeSuccessWithdrawals156a8Regs.
  rewrite writeSuccessMemcpyEndpointLookupOther; try discriminate. exact Hsp.
Qed.

Lemma writeSuccessWithdrawals156a8RegsFacts (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8)) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current).
Proof.
  unfold writeSuccessWithdrawals156a8Regs.
  apply writeSuccessMemcpyEndpointFacts.
Qed.

Lemma writeSuccessWithdrawals156a8RegsPc regs global sp pointer current :
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a8)).
Proof.
  unfold writeSuccessWithdrawals156a8Regs, writeSuccessMemcpyEndpointRegs,
    writeSuccess101dcRegs. rewrite lookup_insert.
  rewrite writeSuccessMemcpyReturnTargetExact; first reflexivity.
  apply bv_eq. native_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderInt156b4RegsX1 (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :
  (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
    withdrawal).1.(seq_regs) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156b4)).
Proof.
  unfold writeSuccessWithdrawalsEncoderInt156b4State,
    writeSuccess156b0After, writeSuccess15694Local, writeSuccess156b0Regs.
  cbn. rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  destruct writeSuccess156b0ValuesExact as (_ & Hlink & _). rewrite Hlink.
  reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderInt156b4RegsX2 (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :
  regs !! "x2" = Some (RVal_Bits sp) ->
  (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
    withdrawal).1.(seq_regs) !! "x2" = Some (RVal_Bits sp).
Proof.
  intros Hsp. unfold writeSuccessWithdrawalsEncoderInt156b4State,
    writeSuccessWithdrawals156b0State, writeSuccessWithdrawals156acState,
    writeSuccess156b0After, writeSuccess156acAfter, writeSuccess156a8After,
    writeSuccess15694Local. cbn.
  rewrite writeSuccess156b0RegsLookupOther; try discriminate.
  rewrite writeSuccess156acRegsLookupOther; try discriminate.
  rewrite writeSuccess156a8RegsLookupOther; try discriminate.
  apply writeSuccessWithdrawals156a8RegsX2. exact Hsp.
Qed.

Lemma writeSuccessWithdrawalsEncoderInt156b4RegsX10 (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :
  (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
    withdrawal).1.(seq_regs) !! "x10" =
    Some (RVal_Bits (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  unfold writeSuccessWithdrawalsEncoderInt156b4State,
    writeSuccess156b0After, writeSuccess15694Local. cbn.
  rewrite writeSuccess156b0RegsLookupOther; try discriminate.
  rewrite writeSuccess156acRegsLookupOther; try discriminate.
  unfold writeSuccess156a8Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. reflexivity.
Qed.

Local Opaque writeSuccessWithdrawals156a8Regs.

Lemma writeSuccessWithdrawalsEncoderInt156b4RegsFacts (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current) ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
      withdrawal).1.(seq_regs).
Proof.
  intros Hfacts. unfold writeSuccessWithdrawalsEncoderInt156b4State,
    writeSuccess156b0After, writeSuccess156acAfter, writeSuccess156a8After,
    writeSuccess15694Local, writeSuccess156b0Regs, writeSuccess156acRegs,
    writeSuccess156a8Regs. cbn.
  repeat (apply writeSuccessOperationalRegisterFactsInsertBit;
    [|discriminate|vm_compute; repeat constructor; discriminate|
      cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessWithdrawalsEncoderInt156b4Boundary (regs : reg_map)
    (global : seq_global_state) (sp pointer : bv 64) (current : list (bv 8))
    (withdrawal : WriteSuccessWithdrawalObservation) :
  writeSuccessWithdrawalsInstructionTable global ->
  IslaInstructionBoundary
    (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
      withdrawal).
Proof.
  intros Htable. split; first reflexivity.
  exists (Z_to_bv 64 0x15d10), a15d10. repeat split.
  - unfold writeSuccessWithdrawalsEncoderInt156b4State,
      writeSuccess156b0After, writeSuccess15694Local, writeSuccess156b0Regs.
    cbn. rewrite lookup_insert.
    destruct writeSuccess156b0ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget. reflexivity.
  - rewrite writeSuccessWithdrawals156a8Instrs. apply Htable.
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Lemma writeSuccessWithdrawals156acPc regs global sp pointer current withdrawal :
  (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)).
Proof.
  unfold writeSuccessWithdrawals156acState, writeSuccess156a8After,
    writeSuccess15694Local, writeSuccess156a8Regs. cbn.
  rewrite lookup_insert writeSuccess156a8NextPcExact. reflexivity.
Qed.

Lemma writeSuccessWithdrawals156acX1 regs global sp pointer current withdrawal oldX1 :
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x1" =
    Some oldX1 ->
  (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).1.(seq_regs) !! "x1" = Some oldX1.
Proof.
  intros Hx1. unfold writeSuccessWithdrawals156acState,
    writeSuccess156a8After, writeSuccess15694Local. cbn.
  rewrite writeSuccess156a8RegsLookupOther; try discriminate. exact Hx1.
Qed.

Lemma writeSuccessWithdrawals156b0Pc regs global sp pointer current withdrawal :
  (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)).
Proof.
  unfold writeSuccessWithdrawals156b0State, writeSuccess156acAfter,
    writeSuccess15694Local, writeSuccess156acRegs. cbn.
  rewrite lookup_insert writeSuccess156acNextPcExact. reflexivity.
Qed.

Lemma writeSuccessWithdrawals156b0X1 regs global sp pointer current withdrawal :
  (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs) !! "x1" = Some (RVal_Bits writeSuccess156b0Ra).
Proof.
  unfold writeSuccessWithdrawals156b0State, writeSuccess156acAfter,
    writeSuccess15694Local, writeSuccess156acRegs. cbn.
  rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  unfold writeSuccess156b0Ra. reflexivity.
Qed.

Lemma writeSuccessWithdrawals156acMstatus regs global sp pointer current withdrawal :
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).1.(seq_regs) writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros H. unfold writeSuccessWithdrawals156acState, writeSuccess156a8After,
    writeSuccess15694Local, writeSuccess15694Mstatus in *. cbn in *.
  rewrite writeSuccess156a8RegsLookupOther; try discriminate. exact H.
Qed.

Lemma writeSuccessWithdrawals156b0Mstatus regs global sp pointer current withdrawal :
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs) writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros H. unfold writeSuccessWithdrawals156b0State, writeSuccess156acAfter,
    writeSuccess15694Local, writeSuccess15694Mstatus in *. cbn in *.
  rewrite writeSuccess156acRegsLookupOther; try discriminate.
  exact (writeSuccessWithdrawals156acMstatus regs global sp pointer current
    withdrawal H).
Qed.

Print Assumptions writeSuccessWithdrawals156a8Instrs.
Print Assumptions writeSuccessWithdrawals156a8RegsX2.
Print Assumptions writeSuccessWithdrawals156a8RegsFacts.
Print Assumptions writeSuccessWithdrawals156a8RegsPc.
Print Assumptions writeSuccessWithdrawalsEncoderInt156b4RegsX1.
Print Assumptions writeSuccessWithdrawalsEncoderInt156b4RegsX2.
Print Assumptions writeSuccessWithdrawals156acPc.
Print Assumptions writeSuccessWithdrawals156acX1.
Print Assumptions writeSuccessWithdrawals156b0Pc.
Print Assumptions writeSuccessWithdrawals156b0X1.
Print Assumptions writeSuccessWithdrawals156acMstatus.
Print Assumptions writeSuccessWithdrawals156b0Mstatus.
Print Assumptions writeSuccessWithdrawalsEncoderInt156b4RegsX10.
Print Assumptions writeSuccessWithdrawalsEncoderInt156b4RegsFacts.
Print Assumptions writeSuccessWithdrawalsEncoderInt156b4Boundary.
