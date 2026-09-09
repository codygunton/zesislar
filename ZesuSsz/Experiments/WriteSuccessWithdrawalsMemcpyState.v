From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ec.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Definition writeSuccessMemcpyByteRegs1 (regs : reg_map) : reg_map :=
  writeSuccess101d8TakenRegs regs.

Definition writeSuccessMemcpyByteRegs2 (regs : reg_map)
    (source index : bv 64) : reg_map :=
  writeSuccess101e0Regs (writeSuccessMemcpyByteRegs1 regs) source index.

Definition writeSuccessMemcpyByteRegs3 (regs : reg_map)
    (source index : bv 64) (byte : bv 8) : reg_map :=
  writeSuccess101e4Regs (writeSuccessMemcpyByteRegs2 regs source index) byte.

Definition writeSuccessMemcpyByteRegs4 (regs : reg_map)
    (source destination index : bv 64) (byte : bv 8) : reg_map :=
  writeSuccess101e8Regs (writeSuccessMemcpyByteRegs3 regs source index byte)
    destination index.

Definition writeSuccessMemcpyByteRegs5 (regs : reg_map)
    (source destination index : bv 64) (byte : bv 8) : reg_map :=
  writeSuccess101ecRegs
    (writeSuccessMemcpyByteRegs4 regs source destination index byte) index.

Definition writeSuccessMemcpyByteRegs6 (regs : reg_map)
    (source destination index : bv 64) (byte : bv 8) : reg_map :=
  writeSuccess101f0Regs
    (writeSuccessMemcpyByteRegs5 regs source destination index byte).

Definition writeSuccessMemcpyByteRegs (regs : reg_map)
    (source destination index : bv 64) (byte : bv 8) : reg_map :=
  writeSuccess101f4Regs
    (writeSuccessMemcpyByteRegs6 regs source destination index byte).

Lemma writeSuccessMemcpyByteRegsLookupOther regs source destination index byte reg :
  reg <> "PC" -> reg <> "x13" -> reg <> "x14" -> reg <> "x15" ->
  writeSuccessMemcpyByteRegs regs source destination index byte !! reg =
    regs !! reg.
Proof.
  intros Hpc Hx13 Hx14 Hx15.
  unfold writeSuccessMemcpyByteRegs, writeSuccessMemcpyByteRegs6,
    writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs4,
    writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs2,
    writeSuccessMemcpyByteRegs1.
  rewrite writeSuccess101f4RegsLookupOther; last exact Hpc.
  rewrite writeSuccess101f0RegsLookupOther; last exact Hpc.
  rewrite writeSuccess101ecRegsLookupOther; [|exact Hpc|exact Hx15].
  rewrite writeSuccess101e8RegsLookupOther; [|exact Hpc|exact Hx14].
  rewrite writeSuccess101e4RegsLookupOther; [|exact Hpc|exact Hx13].
  rewrite writeSuccess101e0RegsLookupOther; [|exact Hpc|exact Hx13].
  unfold writeSuccess101d8TakenRegs. rewrite lookup_insert_ne;
    [reflexivity | congruence].
Qed.

Lemma writeSuccessMemcpyByteRegsX15 regs source destination index byte :
  writeSuccessMemcpyByteRegs regs source destination index byte !! "x15" =
    Some (RVal_Bits (index + BV 64 1)%bv).
Proof.
  unfold writeSuccessMemcpyByteRegs, writeSuccessMemcpyByteRegs6,
    writeSuccessMemcpyByteRegs5.
  rewrite writeSuccess101f4RegsLookupOther; last discriminate.
  rewrite writeSuccess101f0RegsLookupOther; last discriminate.
  unfold writeSuccess101ecRegs.
  rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  reflexivity.
Qed.

Lemma writeSuccessMemcpyByteRegsPc regs source destination index byte :
  writeSuccessMemcpyByteRegs regs source destination index byte !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x101d8)).
Proof.
  unfold writeSuccessMemcpyByteRegs, writeSuccess101f4Regs.
  rewrite lookup_insert. rewrite writeSuccess101f4TargetExact. reflexivity.
Qed.

Lemma writeSuccessMemcpyOperationalInsert regs register (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  In register ["PC"; "x13"; "x14"; "x15"] ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<[register := RVal_Bits value]> regs).
Proof.
  intros Hfacts Hregister.
  eapply writeSuccessOperationalRegisterFactsInsertBit.
  - exact Hfacts.
  - cbn in Hregister. destruct Hregister as [H|[H|[H|[H|[]]]]];
      subst register; discriminate.
  - cbn in Hregister. destruct Hregister as [H|[H|[H|[H|[]]]]];
      subst register; vm_compute; repeat constructor; discriminate.
  - cbn in Hregister. destruct Hregister as [H|[H|[H|[H|[]]]]];
      subst register.
    + left. reflexivity.
    + right. vm_compute. tauto.
    + right. vm_compute. tauto.
    + right. vm_compute. tauto.
Qed.

Lemma writeSuccessMemcpyByteOperationalFacts regs source destination index byte :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs regs source destination index byte).
Proof.
  intros Hfacts.
  unfold writeSuccessMemcpyByteRegs, writeSuccessMemcpyByteRegs6,
    writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs4,
    writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs2,
    writeSuccessMemcpyByteRegs1, writeSuccess101f4Regs,
    writeSuccess101f0Regs, writeSuccess101ecRegs, writeSuccess101e8Regs,
    writeSuccess101e4Regs, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessMemcpyByteRegs2OperationalFacts regs source index :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs2 regs source index).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs2,
    writeSuccessMemcpyByteRegs1, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessMemcpyByteRegs1OperationalFacts regs :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs1 regs).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs1,
    writeSuccess101d8TakenRegs.
  apply writeSuccessMemcpyOperationalInsert; [exact Hfacts | cbn; auto].
Qed.

Lemma writeSuccessMemcpyByteRegs3OperationalFacts regs source index byte :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs3 regs source index byte).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs3,
    writeSuccessMemcpyByteRegs2, writeSuccessMemcpyByteRegs1,
    writeSuccess101e4Regs, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]). exact Hfacts.
Qed.

Lemma writeSuccessMemcpyByteRegs4OperationalFacts regs source destination index byte :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs4 regs source destination index byte).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs4,
    writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs2,
    writeSuccessMemcpyByteRegs1, writeSuccess101e8Regs,
    writeSuccess101e4Regs, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]). exact Hfacts.
Qed.

Lemma writeSuccessMemcpyByteRegs5OperationalFacts regs source destination index byte :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs5 regs source destination index byte).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs5,
    writeSuccessMemcpyByteRegs4, writeSuccessMemcpyByteRegs3,
    writeSuccessMemcpyByteRegs2, writeSuccessMemcpyByteRegs1,
    writeSuccess101ecRegs, writeSuccess101e8Regs,
    writeSuccess101e4Regs, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessMemcpyByteRegs6OperationalFacts regs source destination index byte :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyByteRegs6 regs source destination index byte).
Proof.
  intros Hfacts. unfold writeSuccessMemcpyByteRegs6,
    writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs4,
    writeSuccessMemcpyByteRegs3, writeSuccessMemcpyByteRegs2,
    writeSuccessMemcpyByteRegs1, writeSuccess101f0Regs,
    writeSuccess101ecRegs, writeSuccess101e8Regs,
    writeSuccess101e4Regs, writeSuccess101e0Regs,
    writeSuccess101d8TakenRegs.
  repeat (apply writeSuccessMemcpyOperationalInsert;
    [|cbn; intuition congruence]). exact Hfacts.
Qed.

Print Assumptions writeSuccessMemcpyByteRegsLookupOther.
Print Assumptions writeSuccessMemcpyByteRegsX15.
Print Assumptions writeSuccessMemcpyByteRegsPc.
Print Assumptions writeSuccessMemcpyOperationalInsert.
Print Assumptions writeSuccessMemcpyByteOperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs2OperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs1OperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs3OperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs4OperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs5OperationalFacts.
Print Assumptions writeSuccessMemcpyByteRegs6OperationalFacts.
