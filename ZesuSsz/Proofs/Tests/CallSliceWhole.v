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

(* The call-site step on a call that takes the whole of a held array
   (`CallSlice.zesu_call_slice_whole_step`): decodeParentHeader's first call
   passes its whole input to decodeItem. The step proves the callee's domain
   once, on the window [p, p + length) of offset 0, and keeps it as a
   hypothesis over the array itself; it refuses an array whose length is not
   the call's length word, and an array at another address. *)

Section whole_array.
Context `{!islaG Sigma} `{!threadG}.
Notation SP args := (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (only parsing).
Notation OUT args := (bv_add (bv_add (SP args) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z)) (only parsing).

Lemma call_slice_whole_keeps_domain (args : ParentHeaderArgs) (before0 : list byte)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  Z.of_nat (length (parentHeaderInputBytes args)) = bv_unsigned (parentHeaderInputLength args) ->
  length before0 = 40%nat ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ before0 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs
       [OUT args; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hbefore) "? ? ?".
  zesu_call_slice_whole_step.
  (* the domain is kept, over the array itself *)
  match goal with
  | _ : decodeItemCallDomain (decodeItemCallDataArgs _ _ _ (parentHeaderInputBytes args) before0) |- _ => idtac
  end.
  iFrame.
Qed.

(* No length equation for the array: not a whole-array call (the step
   refuses; the call is then closed from a domain fact the context holds). *)
Lemma call_slice_whole_refused_length (args : ParentHeaderArgs) (before0 : list byte)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length before0 = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs
     [OUT args; parentHeaderInputPointer args; a13; a13; a14; a15; a16; a17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) (parentHeaderInputBytes args) before0) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  bv_unsigned (OUT args) ↦ₘ∗ before0 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs
       [OUT args; parentHeaderInputPointer args; a13; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hbefore Hdom) "Hin Hout HR".
  Fail zesu_call_slice_whole_step.
  iExists (li_pair before0 (li_pair (parentHeaderInputBytes args) tt)).
  cbv [li_fst li_snd].
  iFrame "Hin Hout HR". by iPureIntro.
Qed.

(* The array is held at another spelling of the address: not taken. *)
Lemma call_slice_whole_refused_address (args : ParentHeaderArgs) (before0 : list byte)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  Z.of_nat (length (parentHeaderInputBytes args)) = bv_unsigned (parentHeaderInputLength args) ->
  length before0 = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs
     [OUT args; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) (parentHeaderInputBytes args) before0) ->
  (bv_unsigned (parentHeaderInputPointer args) + 0) ↦ₘ∗ parentHeaderInputBytes args -∗
  bv_unsigned (OUT args) ↦ₘ∗ before0 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs
       [OUT args; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hbefore Hdom) "Hin Hout HR".
  Fail zesu_call_slice_whole_step.
  iExists (li_pair before0 (li_pair (parentHeaderInputBytes args) tt)).
  cbv [li_fst li_snd].
  rewrite Z.add_0_r.
  iFrame "Hin Hout HR". by iPureIntro.
Qed.

(* The block names the output pointer by a local definition (a `LET` binder
   of the generated block) and the output slot is carved from the frame's
   uninitialised region: the step reads the slot's address off the
   definition's body, keeps the domain and states the callee's stack pointer
   over the caller's root word. *)
Lemma call_slice_whole_let_out (args : ParentHeaderArgs)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  let o := OUT args in
  parentHeaderArgsWellFormed args ->
  Z.of_nat (length (parentHeaderInputBytes args)) = bv_unsigned (parentHeaderInputLength args) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400) ↦ₘ? 320 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned o ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs
       [o; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    (bv_unsigned (parentHeaderStackPointer args) - 400) ↦ₘ? 8 ∗
    (bv_unsigned (parentHeaderStackPointer args) - 400 + 8 + 40) ↦ₘ? 272 ∗
    R.
Proof.
  intros o. iIntros (Hwf Hlen) "? ? ?".
  zesu_call_slice_whole_step.
  match goal with
  | _ : decodeItemCallDomain (decodeItemCallDataArgs _ _ _ (parentHeaderInputBytes args) _) |- _ => idtac
  end.
  match goal with
  | _ : zesu_call_slice_addr_fact (bv_unsigned (SP args) = bv_unsigned (parentHeaderStackPointer args) - 400) |- _ => idtac
  end.
  iFrame.
Qed.

(* The array at the input pointer holds other bytes than the caller's
   registered input: the caller's domain lemma does not apply and the step
   refuses. *)
Lemma call_slice_whole_refused_foreign (args : ParentHeaderArgs) (other before0 : list byte)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  Z.of_nat (length other) = bv_unsigned (parentHeaderInputLength args) ->
  length before0 = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs
     [OUT args; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args)) other before0) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ other -∗
  bv_unsigned (OUT args) ↦ₘ∗ before0 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs
       [OUT args; parentHeaderInputPointer args; parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (SP args) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hbefore Hdom) "Hin Hout HR".
  Fail zesu_call_slice_whole_step.
  iExists (li_pair before0 (li_pair other tt)).
  cbv [li_fst li_snd].
  iFrame "Hin Hout HR". by iPureIntro.
Qed.

End whole_array.
