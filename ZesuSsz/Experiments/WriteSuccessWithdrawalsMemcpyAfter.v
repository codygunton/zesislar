From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyIterationMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.

Open Scope Z_scope.

Lemma writeSuccessMemcpyBytesAfterPc (regs : reg_map) (global : seq_global_state)
    (source destination index : bv 64) (bytes : list (bv 8)) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  (writeSuccessMemcpyBytesAfter regs global source destination index bytes).1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)).
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index Hpc; cbn.
  - exact Hpc.
  - apply IH. apply writeSuccessMemcpyByteRegsPc.
Qed.

Lemma writeSuccessMemcpyBytesAfterLookupOther (regs : reg_map)
    (global : seq_global_state) (source destination index : bv 64)
    (bytes : list (bv 8)) register :
  register <> "PC" -> register <> "x13" -> register <> "x14" ->
  register <> "x15" ->
  (writeSuccessMemcpyBytesAfter regs global source destination index bytes).1.(seq_regs) !! register = regs !! register.
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index
    Hpc Hx13 Hx14 Hx15; cbn.
  - reflexivity.
  - rewrite IH; try assumption.
    apply writeSuccessMemcpyByteRegsLookupOther; assumption.
Qed.

Lemma writeSuccessMemcpyBytesAfterX15 (regs : reg_map) (global : seq_global_state)
    (source destination index : bv 64) (bytes : list (bv 8)) :
  regs !! "x15" = Some (RVal_Bits index) ->
  (writeSuccessMemcpyBytesAfter regs global source destination index bytes).1.(seq_regs) !! "x15" =
    Some (RVal_Bits (index + Z_to_bv 64 (Z.of_nat (length bytes)))%bv).
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index Hx15; cbn.
  - replace (index + Z_to_bv 64 0)%bv with index by (apply bv_eq; bv_solve). exact Hx15.
  - rewrite (IH
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv
      (writeSuccessMemcpyByteRegsX15 regs source destination index byte)).
    have Heq :
        ((index + BV 64 1) + Z_to_bv 64 (Z.of_nat (length tail)))%bv =
        (index + Z_to_bv 64 (Z.of_nat (S (length tail))))%bv.
    { apply (proj2 (bv_eq 64 _ _)). bv_solve. }
    rewrite Heq. reflexivity.
Qed.

Lemma writeSuccessMemcpyBytesAfterFacts (regs : reg_map)
    (global : seq_global_state) (source destination index : bv 64)
    (bytes : list (bv 8)) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyBytesAfter regs global source destination index bytes).1.(seq_regs).
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index Hfacts; cbn.
  - exact Hfacts.
  - apply IH. apply writeSuccessMemcpyByteOperationalFacts. exact Hfacts.
Qed.

Lemma writeSuccessMemcpyBytesAfterTable (regs : reg_map)
    (global : seq_global_state) (source destination index : bv 64)
    (bytes : list (bv 8)) :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsInstructionTable
    (writeSuccessMemcpyBytesAfter regs global source destination index bytes).2.
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index Htable; cbn.
  - exact Htable.
  - apply IH. unfold writeSuccess101f0Global. cbn. exact Htable.
Qed.

Print Assumptions writeSuccessMemcpyBytesAfterPc.
Print Assumptions writeSuccessMemcpyBytesAfterLookupOther.
Print Assumptions writeSuccessMemcpyBytesAfterX15.
Print Assumptions writeSuccessMemcpyBytesAfterFacts.
Print Assumptions writeSuccessMemcpyBytesAfterTable.

Lemma writeSuccessMemcpyBytesAfterMemory regs global source destination index
    bytes offset :
  index = Z_to_bv 64 offset ->
  0 <= bv_unsigned destination + offset ->
  bv_unsigned destination + offset + Z.of_nat (length bytes) <= 2 ^ 64 ->
  (writeSuccessMemcpyBytesAfter regs global source destination index bytes).2.(seq_mem) =
    write_mem_list global.(seq_mem) (destination + index)%bv bytes.
Proof.
  revert regs global index offset.
  induction bytes as [|byte tail IH]; intros regs global index offset
    Hindex Hlower Hupper; cbn.
  - reflexivity.
  - rewrite (IH
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv (offset + 1)).
    + unfold writeSuccess101f0Global, writeSuccess101f0Memory. cbn.
      rewrite writeSuccessMemcpyStoredByte. subst index.
      unfold writeSuccessMemcpyDestinationAddress.
      have Hnext :
          (destination + (Z_to_bv 64 offset + BV 64 1))%bv =
          ((destination + Z_to_bv 64 offset) `+Z` 1)%bv.
      { apply (proj2 (bv_eq 64 _ _)). bv_solve. }
      rewrite Hnext. reflexivity.
    + subst index. apply (proj2 (bv_eq 64 _ _)). bv_solve.
    + lia.
    + cbn in Hupper |- *. lia.
Qed.

Print Assumptions writeSuccessMemcpyBytesAfterMemory.

Lemma writeSuccessMemcpyBytesAfterInstrs regs global source destination index bytes :
  ((writeSuccessMemcpyBytesAfter regs global source destination index bytes).2).(seq_instrs) =
    global.(seq_instrs).
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index; cbn.
  - reflexivity.
  - rewrite IH. unfold writeSuccess101f0Global. reflexivity.
Qed.

Print Assumptions writeSuccessMemcpyBytesAfterInstrs.

Lemma writeSuccessMemcpyBytesAfterBoundary regs global source destination index bytes :
  writeSuccessMemcpyBytesAfter regs global source destination index bytes =
    writeSuccess101d8Before
      ((writeSuccessMemcpyBytesAfter regs global source destination index bytes).1).(seq_regs)
      (writeSuccessMemcpyBytesAfter regs global source destination index bytes).2.
Proof.
  revert regs global index.
  induction bytes as [|byte tail IH]; intros regs global index; cbn.
  - reflexivity.
  - apply IH.
Qed.

Print Assumptions writeSuccessMemcpyBytesAfterBoundary.
