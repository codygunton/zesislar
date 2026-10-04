Require Import ZesuSsz.Automation.All.
From Coq Require Import List.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.Switches.ByteFold.
Import ListNotations.

Lemma byte_fold_switch_test (bytes : list byte) (next : byte) :
  bigEndian (bytes ++ [next]) = 256 * bigEndian bytes + bv_unsigned next.
Proof.
  zesu_bigEndian_snoc_if_enabled.
  reflexivity.
Qed.
