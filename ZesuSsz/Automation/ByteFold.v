From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.PureFacts.
Import ListNotations.

(* One byte extends the big-endian value of the prefix. *)
Lemma zesu_bigEndian_snoc (bytes : list byte) (next : byte) :
  bigEndian (bytes ++ [next]) = 256 * bigEndian bytes + bv_unsigned next.
Proof.
  unfold bigEndian.
  rewrite fold_left_app.
  reflexivity.
Qed.

Class ZesuStepByteFold : Prop := zesu_step_byte_fold : True.

Ltac zesu_bigEndian_snoc_if_enabled :=
  let _ := constr:(_ : ZesuStepByteFold) in
  rewrite zesu_bigEndian_snoc.
