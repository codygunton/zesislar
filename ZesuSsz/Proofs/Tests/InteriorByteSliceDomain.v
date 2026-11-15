From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A call's sealed domain (decodeItem's interface) states the input's length,
   the call's argument 2, a symbolic size. The step cannot unfold the domain:
   it reads the size through the registered interface lemma
   decodeItemCallDomainInput and lends the interior slice. *)
Lemma test_interior_byte_slice_domain `{!islaG Sigma} `{!threadG}
    (base start : Z) (bytes before : list (bv 8)) (a0 a1 a2 r3 r4 r5 r6 r7 sp : bv 64) (inputEnd : Z) :
  0 <= start -> start + bv_unsigned a2 <= Z.of_nat (length bytes) ->
  (forall input : list (bv 8), length input = Z.to_nat (bv_unsigned a2) ->
     decodeItemCallDomain
       (decodeItemCallDataArgs [a0; a1; a2; r3; r4; r5; r6; r7] sp inputEnd input before)) ->
  base ↦ₘ∗ bytes -∗
  ∃ x : list (bv 8) *ₗ (),
    (base + start) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain
       (decodeItemCallDataArgs [a0; a1; a2; r3; r4; r5; r6; r7] sp inputEnd x.1ₗ before)⌝ ∗
    ((base + start) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hstart Hfits Hdomain) "Harray".
  pose proof (bv_unsigned_in_range _ a2).
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  apply Hdomain. rewrite length_take length_drop. lia.
Qed.
Print Assumptions test_interior_byte_slice_domain.

(* The size is the one the registered lemma states for the slice: argument 2
   for the call's input, none for another list. The sealed domain itself
   states no size. *)
Goal forall (input other before : list (bv 8)) (a0 a1 a2 r3 r4 r5 r6 r7 sp : bv 64) (inputEnd : Z), True.
Proof.
  intros input other before a0 a1 a2 r3 r4 r5 r6 r7 sp inputEnd.
  let found := zesu_byte_slice_size_in
    (decodeItemCallDomain (decodeItemCallDataArgs [a0; a1; a2; r3; r4; r5; r6; r7] sp inputEnd input before))
    input in
  constr_eq found (bv_unsigned a2).
  Fail let found := zesu_byte_slice_size_in
    (decodeItemCallDomain (decodeItemCallDataArgs [a0; a1; a2; r3; r4; r5; r6; r7] sp inputEnd input before))
    other in
  idtac.
  Fail let found := zesu_byte_slice_size_stated
    (decodeItemCallDomain (decodeItemCallDataArgs [a0; a1; a2; r3; r4; r5; r6; r7] sp inputEnd input before))
    input in
  idtac.
  exact I.
Qed.
