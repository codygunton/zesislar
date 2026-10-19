Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
From Coq Require Import List.
Import ListNotations.

(* A field hint must not identify two different register binders. *)
Goal forall (pointer payload : bv 64) (tail : list byte),
  SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned payload) ++ tail) 0
    (word64Bytes (bv_unsigned payload))) True.
Proof. intros. Fail typeclasses eauto. Abort.

(* The registered fields do not fix an unrelated output array. *)
Goal forall (pointer : bv 64) (output : list byte),
  SimplAnd (fieldImage output 0 (word64Bytes (bv_unsigned pointer))) True.
Proof. intros. Fail typeclasses eauto. Abort.
