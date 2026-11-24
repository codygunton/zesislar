Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderCallSlice.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A guarded pure fact whose guard is a hypothesis is specialised before
   a call-site step looks for its facts (`FactViews.zesu_specialise_guarded_facts`,
   run by `CallSlice.zesu_call_slice`): here the window of the payload a previous
   call returned holds on that call's success, so the caller states it under
   the success test. Without the guard among the hypotheses the step refuses. *)

Goal forall P Q R : Prop, P -> (P -> Q /\ R) -> R.
Proof. intros P Q R HP HPQR. ZesuSsz.Automation2.FactViews.zesu_specialise_guarded_facts. assumption. Qed.

(* A chain of guards, each a hypothesis. *)
Goal forall P1 P2 Q : Prop, P1 -> P2 -> (P1 -> P2 -> Q) -> Q.
Proof. intros P1 P2 Q H1 H2 H. ZesuSsz.Automation2.FactViews.zesu_specialise_guarded_facts. assumption. Qed.

(* A guard that is not a hypothesis: nothing is posed. *)
Goal forall P Q : Prop, (P -> Q) -> True.
Proof.
  intros P Q H. ZesuSsz.Automation2.FactViews.zesu_specialise_guarded_facts.
  Fail (match goal with _ : Q |- _ => idtac end).
  exact I.
Qed.

Section guarded_window.
Context `{!islaG Sigma} `{!threadG}.
Notation W8 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 15%nat bytes (BV 8%N 0%Z)) (List.nth 14%nat bytes (BV 8%N 0%Z)))
    (List.nth 13%nat bytes (BV 8%N 0%Z))) (List.nth 12%nat bytes (BV 8%N 0%Z)))
    (List.nth 11%nat bytes (BV 8%N 0%Z))) (List.nth 10%nat bytes (BV 8%N 0%Z)))
    (List.nth 9%nat bytes (BV 8%N 0%Z))) (List.nth 8%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation LE0 bytes := (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes)))) (only parsing).
Notation SP args := (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (only parsing).
Notation OUT1 args := (bv_add (bv_add (SP args) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z)) (only parsing).
Notation OUT args := (bv_add (bv_add (SP args) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z)) (only parsing).

Lemma call_slice_guarded_window (args : ParentHeaderArgs) (call_after : DecodeItemOutcome)
    (a13 a14 a15 a16 a17 : bv 64) (success : Prop) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length call_after = 40%nat ->
  success ->
  (success ->
   bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (LE0 call_after) /\
   bv_unsigned (LE0 call_after) + bv_unsigned (W8 call_after) <=
     bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (length (parentHeaderInputBytes args))) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ call_after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) ↦ₘ? 272 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (LE0 call_after) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUT args; LE0 call_after; W8 call_after; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hsuccess Hwindow) "? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

(* The guard is not a hypothesis: no window, the step refuses. *)
Lemma call_slice_guarded_window_refused (args : ParentHeaderArgs) (call_after : DecodeItemOutcome)
    (a13 a14 a15 a16 a17 : bv 64) (success : Prop) (slice before1 : list byte) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length call_after = 40%nat ->
  (success ->
   bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (LE0 call_after) /\
   bv_unsigned (LE0 call_after) + bv_unsigned (W8 call_after) <=
     bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (length (parentHeaderInputBytes args))) ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; LE0 call_after; W8 call_after; a13; a14; a15; a16; a17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) slice before1) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  bv_unsigned (LE0 call_after) ↦ₘ∗ slice -∗
  bv_unsigned (OUT args) ↦ₘ∗ before1 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (LE0 call_after) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUT args; LE0 call_after; W8 call_after; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hwindow Hdom) "Hin Hslice Hout HR".
  Fail zesu_call_slice_step.
  iExists (li_pair before1 (li_pair slice tt)).
  cbv [li_fst li_snd].
  iFrame "Hslice Hout HR". by iPureIntro.
Qed.

End guarded_window.
