From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import IslaTraces.write_success_94.a156d0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsOutputEntry regs global (data : bv 64) :
    IslaState :=
  writeSuccess156ccAfter
    (writeSuccess156c8Regs
      (writeSuccess156c4Regs (writeSuccess156c0Regs regs) data)) global.

Lemma writeSuccessWithdrawalsOutputEntryRegsFacts regs global data :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawalsOutputEntry regs global data).1.(seq_regs).
Proof.
  intros Hfacts.
  unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
    writeSuccess15694Local, writeSuccess156ccRegs, writeSuccess156c8Regs,
    writeSuccess156c4Regs, writeSuccess156c0Regs. cbn.
  repeat (apply writeSuccessOperationalRegisterFactsInsertBit;
    [|discriminate|vm_compute; repeat constructor; discriminate|
      cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessWithdrawalsOutputEntryInv regs global data bytes priorLog :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  length bytes = 20%nat ->
  read_mem_list global.(seq_mem) (bv_unsigned data) 20%N = Some bytes ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  Inv_write_output data (BV 64 20) (Z_to_bv 64 0x156d0) bytes priorLog
    (writeSuccessWithdrawalsOutputEntry regs global data, priorLog).
Proof.
  intros Htable Hfacts Hlength Hread Hmmio.
  unfold Inv_write_output.
  repeat lazymatch goal with |- _ /\ _ => split end.
  - split; first reflexivity.
    exists (Z_to_bv 64 0x10190), a10190. repeat split.
    + unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
        writeSuccess15694Local. cbn. unfold writeSuccess156ccRegs.
      rewrite lookup_insert. destruct writeSuccess156ccValuesExact as
        (_ & _ & _ & Htarget). rewrite Htarget. reflexivity.
    + apply Htable. cbn. tauto.
  - reflexivity.
  - unfold writeSuccessWithdrawalsConcretePc,
      writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
      writeSuccess15694Local. cbn. unfold writeSuccess156ccRegs.
    rewrite lookup_insert. destruct writeSuccess156ccValuesExact as
      (_ & _ & _ & Htarget). rewrite Htarget. reflexivity.
  - unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
      writeSuccess15694Local, writeSuccess156ccRegs. cbn.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    destruct writeSuccess156ccValuesExact as (_ & Hlink & _).
    rewrite Hlink. reflexivity.
  - unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    unfold writeSuccess156c4Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. have -> : (data + BV 64 0)%bv = data by bv_solve.
    reflexivity.
  - unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    unfold writeSuccess156c0Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. reflexivity.
  - apply bv_eq. native_compute. reflexivity.
  - exists a156d0. apply Htable. cbn. tauto.
  - rewrite bv_unsigned_BV. cbn. lia.
  - rewrite Hlength. exact Hread.
  - exact Htable.
  - apply writeSuccessWithdrawalsOutputEntryRegsFacts. exact Hfacts.
  - exact Hmmio.
  - reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsOutputEntryRegsFacts.
Print Assumptions writeSuccessWithdrawalsOutputEntryInv.
