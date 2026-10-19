Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
From Coq Require Import List.
Import ListNotations.

Lemma pointer_control (p l : bv 64) (tail : list byte) :
 SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned p) ++
 bv_to_little_endian 8 8 (bv_unsigned l) ++ tail) 0 (word64Bytes (bv_unsigned p))) True.
Proof. typeclasses eauto. Qed.
Lemma length_control (p l : bv 64) (tail : list byte) :
 SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned p) ++
 bv_to_little_endian 8 8 (bv_unsigned l) ++ tail) 8 (word64Bytes (bv_unsigned l))) True.
Proof. typeclasses eauto. Qed.

Goal forall (p l : bv 64) (tail : list byte),
  SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned p) ++
  bv_to_little_endian 8 8 (bv_unsigned l) ++ tail) 8 (word64Bytes (bv_unsigned p))) True.
Proof. intros. Fail typeclasses eauto. Abort.
