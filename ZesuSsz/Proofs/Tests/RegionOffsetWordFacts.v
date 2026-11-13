From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A callee frame below a stack word, inside a larger frame region. The
   region base reads `bv_unsigned word`; the frame address reads
   `bv_unsigned (bv_add word (-400))`. Only the word's lower bound shows that
   the offset does not wrap, and that bound sits folded in a predicate over
   the record the word is read from. *)
Record OffsetWordArgs := { offsetWord : bv 64; offsetOther : bv 64 }.

Definition offsetWordWellFormed (args : OffsetWordArgs) : Prop :=
  bv_unsigned (offsetOther args) < 64 /\
  0xa0000000 + 512 <= bv_unsigned (offsetWord args) /\
  bv_unsigned (offsetWord args) < 0xc0000000.

Check ZesuSsz.Automation2.UninitRegions.ZesuRegionBounds.

Lemma region_offset_word_contained (args : OffsetWordArgs) :
  offsetWordWellFormed args ->
  ZesuSsz.Automation2.UninitRegions.ZesuRegionBounds
    (0 <= 16 /\
     bv_unsigned (offsetWord args) - 400 - 112 <=
       bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 /\
     bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 + 16 <=
       bv_unsigned (offsetWord args) - 400 - 112 + 112).
Proof. intros Hwf. typeclasses eauto. Qed.

(* The same frame at offset -300 lies outside the region. *)
Lemma region_offset_word_outside (args : OffsetWordArgs) :
  offsetWordWellFormed args -> True.
Proof.
  intros Hwf.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionBounds
    (0 <= 16 /\
     bv_unsigned (offsetWord args) - 400 - 112 <=
       bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551316)) - 16 /\
     bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551316)) - 16 + 16 <=
       bv_unsigned (offsetWord args) - 400 - 112 + 112)) in idtac.
  exact I.
Qed.

(* Without the word's lower bound the offset may wrap: no containment. *)
Lemma region_offset_word_needs_bound (args : OffsetWordArgs) :
  bv_unsigned (offsetOther args) < 64 -> True.
Proof.
  intros Hother.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionBounds
    (0 <= 16 /\
     bv_unsigned (offsetWord args) - 400 - 112 <=
       bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 /\
     bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 + 16 <=
       bv_unsigned (offsetWord args) - 400 - 112 + 112)) in idtac.
  exact I.
Qed.
