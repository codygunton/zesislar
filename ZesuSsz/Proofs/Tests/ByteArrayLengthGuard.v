From Coq Require Import ZArith.ZArith Lists.List.
From stdpp Require Import list bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Import ListNotations.
Local Open Scope Z_scope.

(* The assembler's conversion steps compare list lengths only through
   `zesu_byte_array_length_literal`. A spine that no variable decides gives
   its numeral; a spine stuck on a variable is refused before any
   evaluation (decodeParentHeader 046c: a frame slot updated at a count
   `Z.to_nat (bv_unsigned …)`, whose VM read-back normalised every open byte
   and ran out of memory). *)
Goal forall (w x : bv 64) (b : bv 8), True.
Proof.
  intros w x b.
  (* Evaluated: explicit cells, a little-endian word, closed take, drop, insert. *)
  let c := ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_length_literal
    constr:([b; b] ++ bv_to_little_endian 8 8 (bv_unsigned w)) in
  constr_eq c 10%nat.
  let c := ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_length_literal
    constr:(take 3 [b; b; b; b] ++ b :: drop 2 [b; b; b]) in
  constr_eq c 5%nat.
  let c := ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_length_literal
    constr:(<[1%nat := bv_extract 0 8 (w + x)]> [b; b; b]) in
  constr_eq c 3%nat.
  exact I.
Qed.

Goal forall (w x : bv 64) (b : bv 8) (l : list (bv 8)), True.
Proof.
  intros w x b l.
  (* Refused: a list binder, and a count stuck on a variable. *)
  Fail let c := ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_length_literal
    constr:(l) in idtac.
  Fail let c := ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_length_literal
    constr:(take (Z.to_nat (bv_unsigned (w + x) - bv_unsigned w))
      [bv_extract 0 8 (w + x); b] ++ b :: [b]) in idtac.
  exact I.
Qed.
