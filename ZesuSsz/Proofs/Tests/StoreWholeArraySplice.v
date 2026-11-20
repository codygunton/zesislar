Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A store that covers a whole held array (`StoreMemoryLookup.v`,
   `zesu_store_whole_array_splice`): the held array is the splice
   `take k J ++ b0 :: … :: b7 :: drop (k + 8) J` of an 8-byte array `J`, the
   store pointer is a closed-offset chain over the stack root word that
   equals the array's address. Where the goal requests an array there, the
   held array becomes the stored bytes. *)
Section store_whole_array.
Context `{!islaG Sigma} `{!threadG}.
Notation ROOT args := (bv_unsigned (parentHeaderStackPointer args)) (only parsing).
Notation PTR args c := (bv_add (bv_add (bv_add (parentHeaderStackPointer args)
  (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N c)) (only parsing).

Lemma store_whole_array_splice_fires (args : ParentHeaderArgs) (J : list (bv 8)) (w : bv 64) :
  parentHeaderArgsWellFormed args ->
  length J = 8%nat ->
  (ROOT args - 400 + 48) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48))) J ++
     bv_extract 0 8 w :: bv_extract 8 8 w :: bv_extract 16 8 w :: bv_extract 24 8 w ::
     bv_extract 32 8 w :: bv_extract 40 8 w :: bv_extract 48 8 w :: bv_extract 56 8 w ::
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48)) + N.to_nat 8) J) -∗
  ∃ x : bv 64,
    (ROOT args - 400 + 48) ↦ₘ∗
      [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
       bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w] ∗ ⌜x = w⌝.
Proof.
  iIntros (Hwf HJ) "HJ".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_whole_array_splice.
  iExists w. iFrame. done.
Qed.

(* The stored bytes as the store wrote them (`bv_to_little_endian 8 8
   (bv_unsigned w)`), the goal asks for `w`'s byte extracts: the held array
   is presented in the requested spelling. *)
Lemma store_whole_array_splice_word (args : ParentHeaderArgs) (J : list (bv 8)) (w : bv 64) :
  parentHeaderArgsWellFormed args ->
  length J = 8%nat ->
  (ROOT args - 400 + 48) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48))) J ++
     bv_to_little_endian 8 8 (bv_unsigned w) ++
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48)) + N.to_nat 8) J) -∗
  ∃ x : bv 64,
    (ROOT args - 400 + 48) ↦ₘ∗
      [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
       bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w] ∗ ⌜x = w⌝.
Proof.
  iIntros (Hwf HJ) "HJ".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_whole_array_splice.
  iExists w. iFrame. done.
Qed.

(* Guard: the store sits 8 bytes into a 16-byte array (offset not 0). *)
Lemma store_whole_array_splice_offset (args : ParentHeaderArgs) (J : list (bv 8)) (w : bv 64) :
  parentHeaderArgsWellFormed args ->
  length J = 16%nat ->
  (ROOT args - 400 + 40) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 40))) J ++
     bv_extract 0 8 w :: bv_extract 8 8 w :: bv_extract 16 8 w :: bv_extract 24 8 w ::
     bv_extract 32 8 w :: bv_extract 40 8 w :: bv_extract 48 8 w :: bv_extract 56 8 w ::
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 40)) + N.to_nat 8) J) -∗
  ∃ x : bv 64,
    (ROOT args - 400 + 40) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 40))) J ++
     bv_extract 0 8 w :: bv_extract 8 8 w :: bv_extract 16 8 w :: bv_extract 24 8 w ::
     bv_extract 32 8 w :: bv_extract 40 8 w :: bv_extract 48 8 w :: bv_extract 56 8 w ::
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 40)) + N.to_nat 8) J) ∗
    ⌜x = w⌝.
Proof.
  iIntros (Hwf HJ) "HJ".
  Fail ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_whole_array_splice.
  iExists w. iFrame. done.
Qed.

(* Guard: offset 0 but the array is longer than the store (16 bytes): the
   tail of `J` stays. *)
Lemma store_whole_array_splice_longer (args : ParentHeaderArgs) (J : list (bv 8)) (w : bv 64) :
  parentHeaderArgsWellFormed args ->
  length J = 16%nat ->
  (ROOT args - 400 + 48) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48))) J ++
     bv_extract 0 8 w :: bv_extract 8 8 w :: bv_extract 16 8 w :: bv_extract 24 8 w ::
     bv_extract 32 8 w :: bv_extract 40 8 w :: bv_extract 48 8 w :: bv_extract 56 8 w ::
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48)) + N.to_nat 8) J) -∗
  ∃ x : bv 64,
    (ROOT args - 400 + 48) ↦ₘ∗
    (take (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48))) J ++
     bv_extract 0 8 w :: bv_extract 8 8 w :: bv_extract 16 8 w :: bv_extract 24 8 w ::
     bv_extract 32 8 w :: bv_extract 40 8 w :: bv_extract 48 8 w :: bv_extract 56 8 w ::
     drop (Z.to_nat (bv_unsigned (PTR args 18446744073709551264%Z) - (ROOT args - 400 + 48)) + N.to_nat 8) J) ∗
    ⌜x = w⌝.
Proof.
  iIntros (Hwf HJ) "HJ".
  Fail ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_whole_array_splice.
  iExists w. iFrame. done.
Qed.
End store_whole_array.

Print Assumptions store_whole_array_splice_fires.
