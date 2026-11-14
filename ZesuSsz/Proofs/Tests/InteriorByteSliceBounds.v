Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A caller hands a callee the rest of an input slice after the bytes an
   earlier call consumed: start and size are symbolic. The bounds follow from
   the earlier call's domain and post (its consumed count) by derived facts. *)
Section bounds.
Context (base cursor remaining a0 r3 r4 r5 r6 r7 sp : bv 64) (inputEnd : Z).
Context (bytes before after : list byte).
Context (Hdomain : decodeItemC1BDomain
  (decodeItemCallDataArgs [a0; cursor; remaining; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned remaining))
       (drop (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) bytes)) before)).
Context (Hpost : DecodeMeaningModuloKnownBugs
  (decodeItemCallDataArgs [a0; cursor; remaining; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned remaining))
       (drop (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) bytes)) before) after).
Context (Hlow : bv_unsigned base <= bv_unsigned cursor)
  (Hhigh : bv_unsigned cursor <= bv_unsigned base + Z.of_nat (length bytes)).

Lemma test_interior_byte_slice_symbolic_start :
  bv_unsigned base +
    Z.of_nat (Z.to_nat (bv_unsigned (cursor + listWord64At24 after) - bv_unsigned base)) =
  bv_unsigned (cursor + listWord64At24 after).
Proof using All. zesu_byte_slice_bound_arith. Qed.

Lemma test_interior_byte_slice_symbolic_bounds :
  (Z.to_nat (bv_unsigned (cursor + listWord64At24 after) - bv_unsigned base) +
   Z.to_nat (bv_unsigned (remaining - listWord64At24 after)) <= length bytes)%nat.
Proof using All. zesu_byte_slice_bound_arith. Qed.
End bounds.
