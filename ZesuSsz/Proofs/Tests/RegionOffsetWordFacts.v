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

(* A load through a frame pointer: the address offsets the word three times
   (word - 400 + 400 - 360) and lands 32 bytes into a 40-byte array that
   starts 8 bytes above `word - 400`. *)
Lemma region_offset_word_chain_in_array (args : OffsetWordArgs) (values : list (bv 8)) :
  offsetWordWellFormed args -> length values = 40%nat ->
  ZesuSsz.Automation2.UninitRegions.ZesuRegionBounds
    (bv_unsigned (offsetWord args) - 400 + 8 <=
       bv_unsigned (bv_add (bv_add (bv_add (offsetWord args) (BV 64 18446744073709551216))
         (BV 64 400)) (BV 64 18446744073709551256)) <
       bv_unsigned (offsetWord args) - 400 + 8 + Z.of_nat (length values) * Z.of_N (8 `div` 8)%N \/
     bv_unsigned (offsetWord args) - 400 + 8 =
       bv_unsigned (bv_add (bv_add (bv_add (offsetWord args) (BV 64 18446744073709551216))
         (BV 64 400)) (BV 64 18446744073709551256))).
Proof. intros Hwf Hlength. typeclasses eauto. Qed.

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

(* The offset-word attempt runs on this goal (the guard fires) but the bound
   is unprovable, so the attempt fails as a whole: no fact selection or
   cleared hypothesis survives, and the caller's goal and context stay as
   they were. *)
Lemma region_offset_word_unprovable_no_commit (args : OffsetWordArgs) :
  bv_unsigned (offsetOther args) < 64 ->
  (0 <= 16 /\
   bv_unsigned (offsetWord args) - 400 - 112 <=
     bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 /\
   bv_unsigned (bv_add (offsetWord args) (BV 64 18446744073709551216)) - 16 + 16 <=
     bv_unsigned (offsetWord args) - 400 - 112 + 112) \/
  bv_unsigned (offsetOther args) < 64.
Proof.
  intros Hother.
  assert_succeeds (left; ZesuSsz.Automation2.UninitRegions.zesu_region_offset_candidate).
  Fail (left; ZesuSsz.Automation2.UninitRegions.zesu_region_bounds).
  try (left; ZesuSsz.Automation2.UninitRegions.zesu_region_bounds).
  right. exact Hother.
Qed.
