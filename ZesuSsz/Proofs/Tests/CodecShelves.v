Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From stdpp Require Import list list_numbers bitvector.definitions.
From Coq Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma codec_shelf_bytes (word : bv 64) (address : Z)
    (Haddress : 0 <= address < 2 ^ 64) :
  SHELVED_SIDECOND
    (bv_to_little_endian 8 8 (bv_unsigned word) ++
       bv_to_little_endian 8 8 address =
     bytes_of_u64s [word; Z_to_bv 64 address]).
Proof. ZesuSsz.Automation2.Finish.zesu_finish_v1. Qed.

Lemma codec_shelf_zero_offset (base : Z) (word : bv 64)
    (suffix : list (bv 8)) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + -16 + 0 - (base - 16)))
      (bv_to_little_endian 8 8 (bv_unsigned word) ++ suffix)))) = word.
Proof.
  ZesuSsz.Automation2.Finish.zesu_finish_zero_offset_u64_roundtrip.
Qed.

Lemma codec_shelf_nonzero_offset (word : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat 1)
      (BV 8 0 :: bv_to_little_endian 8 8 (bv_unsigned word))))) = word.
Proof.
  Fail ZesuSsz.Automation2.Finish.zesu_finish_zero_offset_u64_roundtrip.
  cbn [Z.to_nat drop].
  apply ZesuSsz.Automation2.ByteArrays.zesu_u64_little_endian_roundtrip.
Qed.

Lemma codec_shelf_symbolic_offset (offset : Z) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat offset) ([] : list (bv 8))))) = BV 64 0.
Proof.
  Fail ZesuSsz.Automation2.Finish.zesu_finish_zero_offset_u64_roundtrip.
  rewrite drop_nil.
  cbn [take little_endian_to_bv little_endian_to_Z fmap list_fmap List.map].
  apply bv_eq. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Print Assumptions codec_shelf_bytes.
Print Assumptions codec_shelf_zero_offset.
Print Assumptions codec_shelf_nonzero_offset.
Print Assumptions codec_shelf_symbolic_offset.

Lemma codec_shelf_list_atom (bytes : list (bv 8))
    (Hlength : length bytes = 40%nat) :
  exists head tail, bytes = head :: tail /\ length tail = 39%nat.
Proof. zesu_finish_list_cons_atom. Qed.

Lemma codec_shelf_atom_refuses_proposition : True.
Proof.
  time "atom_refuse_proposition" (tryif zesu_finish_list_cons_atom then fail 1 else idtac).
  exact I.
Qed.

Lemma codec_shelf_atom_refuses_equality : (0 = 0)%Z.
Proof.
  time "atom_refuse_equality" (tryif zesu_finish_list_cons_atom then fail 1 else idtac).
  reflexivity.
Qed.
