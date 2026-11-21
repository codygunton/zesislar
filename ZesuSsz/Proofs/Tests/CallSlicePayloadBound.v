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

(* The window of a call on the payload the previous call returned, when the
   context holds no bound on the payload length: the caller's contract bounds
   the payload of a call on its whole input
   (`ZesuCallSliceCallerPayloadBound`, decodeParentHeader's instance from
   `parentHeaderOuterPayloadBound`). Refused when the previous call's input is
   not the caller's input. *)

Section payload_bound.
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

Lemma call_slice_payload_bound_from_contract (args : ParentHeaderArgs) (call_after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length call_after = 40%nat ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT1 args; parentHeaderInputPointer args; parentHeaderInputLength args; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) (parentHeaderInputBytes args) before0) call_after ->
  bv_unsigned (W8 call_after) <> 0%Z ->
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
  iIntros (Hwf Hlen Hmean Hnz) "? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

(* The previous call read another list than the caller's input: the
   contract's bound does not apply and the step refuses. *)
Lemma call_slice_payload_bound_refused (args : ParentHeaderArgs) (input slice : list byte)
    (call_after before0 before1 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length call_after = 40%nat ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT1 args; parentHeaderInputPointer args; parentHeaderInputLength args; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) input before0) call_after ->
  bv_unsigned (W8 call_after) <> 0%Z ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; LE0 call_after; W8 call_after; a13; a14; a15; a16; a17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) slice before1) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ input -∗
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
  iIntros (Hwf Hlen Hmean Hnz Hdom) "Hin Hslice Hout HR".
  Fail zesu_call_slice_step.
  iExists (li_pair before1 (li_pair slice tt)).
  cbv [li_fst li_snd].
  iFrame "Hslice Hout HR". by iPureIntro.
Qed.

End payload_bound.
