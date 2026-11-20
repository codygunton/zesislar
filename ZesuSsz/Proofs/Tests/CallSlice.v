Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderCallSlice.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.NextUint64CallSlice.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderNextUint64Slice.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The call-site step (`Automation2/CallSlice.v`) at the existential of
   decodeItem's call spec, called from decodeParentHeader. Each goal is one
   way the step finds the window of the input slice. *)

Notation cs_word0 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 7%nat bytes (BV 8%N 0%Z)) (List.nth 6%nat bytes (BV 8%N 0%Z)))
    (List.nth 5%nat bytes (BV 8%N 0%Z))) (List.nth 4%nat bytes (BV 8%N 0%Z)))
    (List.nth 3%nat bytes (BV 8%N 0%Z))) (List.nth 2%nat bytes (BV 8%N 0%Z)))
    (List.nth 1%nat bytes (BV 8%N 0%Z))) (List.nth 0%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation cs_word8 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 15%nat bytes (BV 8%N 0%Z)) (List.nth 14%nat bytes (BV 8%N 0%Z)))
    (List.nth 13%nat bytes (BV 8%N 0%Z))) (List.nth 12%nat bytes (BV 8%N 0%Z)))
    (List.nth 11%nat bytes (BV 8%N 0%Z))) (List.nth 10%nat bytes (BV 8%N 0%Z)))
    (List.nth 9%nat bytes (BV 8%N 0%Z))) (List.nth 8%nat bytes (BV 8%N 0%Z))) (only parsing).

(* Window stated by the entry for the previous call, advanced by its consumed
   count; output slot carved out of an uninitialised region. *)
Section window_advanced.
Context `{!islaG Sigma} `{!threadG}.
Notation W24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation OUT args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z)) (only parsing).
Notation OUT2 args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z)) (only parsing).
Lemma call_slice_window_advanced (args : ParentHeaderArgs) (x19 x18 : bv 64) (call2_after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned x19)%Z ->
  (bv_unsigned x19 + bv_unsigned x18 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  length call2_after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) call2_after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ before0 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 16) ↦ₘ∗ call2_after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56) ↦ₘ? 216 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (bv_add x19 (W24 call2_after)) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT2 args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUT2 args; bv_add x19 (W24 call2_after); bv_sub x18 (W24 call2_after); a13; a14; a15; a16; a17]
       (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlo Hhi Hlen Hdom Hmean) "? ? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

(* The same call after Lithium let-bound the proof-mode environment
   (`let_bind_envs`, `IPM_JANNO`): the step substitutes the binding back and
   fires; without that it sees no held array and the interior-slice lend takes
   the existential instead. *)
Lemma call_slice_aliased_environment (args : ParentHeaderArgs) (x19 x18 : bv 64) (call2_after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned x19)%Z ->
  (bv_unsigned x19 + bv_unsigned x18 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  length call2_after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) call2_after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ before0 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 16) ↦ₘ∗ call2_after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56) ↦ₘ? 216 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (bv_add x19 (W24 call2_after)) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT2 args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUT2 args; bv_add x19 (W24 call2_after); bv_sub x18 (W24 call2_after); a13; a14; a15; a16; a17]
       (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlo Hhi Hlen Hdom Hmean) "? ? ? ? ?".
  let_bind_envs.
  lazymatch goal with |- environments.envs_entails ?e _ => is_var e end.
  zesu_call_slice_step.
  iFrame.
Qed.
End window_advanced.

(* Window of the previous call's payload, its pointer in the load form, with
   the no-wrap fact; output slot carved at distance 0. *)
Section payload_load_form.
Context `{!islaG Sigma} `{!threadG}.
Notation W8 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 15%nat bytes (BV 8%N 0%Z)) (List.nth 14%nat bytes (BV 8%N 0%Z)))
    (List.nth 13%nat bytes (BV 8%N 0%Z))) (List.nth 12%nat bytes (BV 8%N 0%Z)))
    (List.nth 11%nat bytes (BV 8%N 0%Z))) (List.nth 10%nat bytes (BV 8%N 0%Z)))
    (List.nth 9%nat bytes (BV 8%N 0%Z))) (List.nth 8%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation LE0 bytes := (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes)))) (only parsing).
Notation OUT1 args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z)) (only parsing).
Notation OUT args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z)) (only parsing).
Lemma call_slice_payload_load_form (args : ParentHeaderArgs) (call_after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  length call_after = 40%nat ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT1 args; parentHeaderInputPointer args; parentHeaderInputLength args; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (parentHeaderInputBytes args) before0) call_after ->
  bv_unsigned (W8 call_after) <> 0%Z ->
  (bv_unsigned (W8 call_after) < 18446744073709551607)%Z ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ call_after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) ↦ₘ? 272 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (LE0 call_after) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUT args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUT args; LE0 call_after; W8 call_after; a13; a14; a15; a16; a17]
       (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlen Hmean Hnz Hlt) "? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.
End payload_load_form.

(* No window fact: the window of (x19, x18) is derived from call 1's meaning
   and call 2's domain, then advanced; output slot is a held array. *)
Section payload_window_derived.
Context `{!islaG Sigma} `{!threadG}.
Notation W24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).
Lemma call_slice_payload_window_derived (args : ParentHeaderArgs) (x19 x18 : bv 64) (call2_after : DecodeItemOutcome) (before0 before1 : list byte) (call_after : DecodeItemOutcome)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  decodeItemCallMeaning (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); parentHeaderInputPointer args; parentHeaderInputLength args; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) (parentHeaderInputBytes args) before1) call_after ->
  zesu_named_eq x19 (cs_word0 call_after) -> zesu_named_eq x18 (cs_word8 call_after) ->
  bv_unsigned (cs_word8 call_after) <> 0%Z ->
  length call2_after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) call2_after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ before0 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 16) ↦ₘ∗ call2_after -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (bv_add x19 (W24 call2_after)) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z)) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); bv_add x19 (W24 call2_after); bv_sub x18 (W24 call2_after); a13; a14; a15; a16; a17]
       (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hmean1 Hn1 Hn2 Hnz Hlen Hdom Hmean) "? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.
End payload_window_derived.

(* The consumed count in the 8-byte load form. *)
Section consumed_load_form.
Context `{!islaG Sigma} `{!threadG}.
Notation W24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation LE24 bytes := (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 24 bytes)))) (only parsing).
Lemma call_slice_consumed_load_form (args : ParentHeaderArgs) (x19 x18 : bv 64) (call2_after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned x19)%Z ->
  (bv_unsigned x19 + bv_unsigned x18 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  length call2_after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); x19; x18; b13; b14; b15; b16; b17]
     (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) call2_after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 8) ↦ₘ∗ before0 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 16) ↦ₘ∗ call2_after -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (bv_add x19 (LE24 call2_after)) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z)) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); bv_add x19 (LE24 call2_after); bv_sub x18 (LE24 call2_after); a13; a14; a15; a16; a17]
       (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (bv_unsigned (parentHeaderInputEnd args)) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlo Hhi Hlen Hdom Hmean) "? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.
End consumed_load_form.

(* The step refuses an existential that is not a call spec's: a one-list lend
   stays with the interior-slice lend. *)
Section not_a_call.
Context `{!islaG Sigma} `{!threadG}.
Lemma call_slice_not_a_call (base : Z) (bytes : list (bv 8)) (tail : spec) :
  length bytes = 592%nat ->
  base ↦ₘ∗ bytes -∗ spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    (base + 152)%Z ↦ₘ∗ x.2ₗ ∗ spec_trace x.1ₗ ∗
    ⌜32%Z = Z.of_nat (length x.2ₗ)⌝ ∗
    ((base + 152)%Z ↦ₘ∗ x.2ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hlength) "Harray Htrace".
  Fail zesu_call_slice_step.
  ZesuSsz.Automation2.InteriorByteSlice.zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  rewrite length_take length_drop. lia.
Qed.
End not_a_call.

(* Early restore: at an existential goal, a restore wand whose borrowed slice
   is back in the context is applied; with the slice absent, or at a goal that
   is not an existential, the step does not run. *)
Section early_restore.
Context `{!islaG Sigma} `{!threadG}.
Lemma call_early_restore_fires (a b : Z) (whole slice : list byte) :
  ((b ↦ₘ∗ slice) -∗ (a ↦ₘ∗ whole)) -∗ (b ↦ₘ∗ slice) -∗
  ∃ n : Z, (a ↦ₘ∗ whole) ∗ ⌜n = 0⌝.
Proof.
  iIntros "Hr Hs".
  zesu_call_early_restore.
  iExists 0. iFrame. done.
Qed.

Lemma call_early_restore_skipped (a b : Z) (whole slice : list byte) :
  ((b ↦ₘ∗ slice) -∗ (a ↦ₘ∗ whole)) -∗ (b ↦ₘ∗ slice) -∗
  (a ↦ₘ∗ whole).
Proof.
  iIntros "Hr Hs".
  Fail zesu_call_early_restore.
  iApply ("Hr" with "Hs").
Qed.

Lemma call_early_restore_no_slice (a b : Z) (whole slice : list byte) :
  ((b ↦ₘ∗ slice) -∗ (a ↦ₘ∗ whole)) -∗
  ∃ n : Z, ((b ↦ₘ∗ slice) -∗ (a ↦ₘ∗ whole)) ∗ ⌜n = 0⌝.
Proof.
  iIntros "Hr".
  Fail zesu_call_early_restore.
  iExists 0. iFrame. done.
Qed.
End early_restore.

(* A pointer and a length the caller stored byte by byte and reloaded, read
   back as integer words (`WrappedWord.zesu_word_explicit_list_rewrite`): the
   window of the slice is linear arithmetic over the range facts. Without a
   range fact no window is derived. *)
Lemma call_slice_integer_window (z : Z) (bytes : list (bv 8)) :
  0 <= z -> z + Z.of_nat (length bytes) < 2 ^ 64 ->
  z <= bv_unsigned (Z_to_bv 64 z) /\
  bv_unsigned (Z_to_bv 64 z) + bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))) <=
    z + Z.of_nat (length bytes).
Proof.
  intros Hz Hend.
  zesu_call_slice_window decodeItemCallSliceInterface decodeItemCallDomain decodeItemCallMeaning
    decodeItemCallDataArgs (Z_to_bv 64 z) (Z_to_bv 64 (Z.of_nat (length bytes))) z bytes
    ltac:(fun Hw => exact Hw).
Qed.
Goal forall (z : Z) (bytes : list (bv 8)), True.
Proof.
  intros z bytes.
  Fail zesu_call_slice_window decodeItemCallSliceInterface decodeItemCallDomain decodeItemCallMeaning
    decodeItemCallDataArgs (Z_to_bv 64 z) (Z_to_bv 64 (Z.of_nat (length bytes))) z bytes
    ltac:(fun Hw => idtac).
  exact I.
Qed.

(* nextUint64's first call: the input pointer and length are integer words,
   the output slot is 40 bytes at offset 8 of the uninitialised 48 bytes at
   `sp - 96`, the input end is the register word `Z_to_bv 64 ie`. The domain
   was split by an earlier step (`zesu_split_folded_pure`); it stays in the
   context folded, so the callee domain is proved from it. *)
Section first_call_integer_root.
Context `{!islaG Sigma} `{!threadG}.
Notation SPW args := (Z_to_bv 64 (ParentHeaderRootFacts.nextStackPointer (nextUint64Base args))) (only parsing).
Notation OUTW args := (bv_add (bv_add (bv_add (SPW args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 96%Z)) (BV 64%N 18446744073709551528%Z)) (only parsing).
Notation IPW args := (Z_to_bv 64 (ParentHeaderRootFacts.nextInputPointer (nextUint64Base args))) (only parsing).
Notation ILW args := (Z_to_bv 64 (Z.of_nat (length (ParentHeaderRootFacts.nextInputBytes (nextUint64Base args))))) (only parsing).
Lemma call_slice_first_call_integer_root (args : NextUint64Args) (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  nextUint64BoundaryDomain args ->
  ParentHeaderRootFacts.nextInputPointer (nextUint64Base args) ↦ₘ∗ ParentHeaderRootFacts.nextInputBytes (nextUint64Base args) -∗
  (ParentHeaderRootFacts.nextStackPointer (nextUint64Base args) - 96) ↦ₘ? 48 -∗
  R -∗
  ∃ x : list byte *ₗ list byte *ₗ (),
    bv_unsigned (IPW args) ↦ₘ∗ x.2ₗ ∗
    bv_unsigned (OUTW args) ↦ₘ∗ x.1ₗ ∗
    ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUTW args; IPW args; ILW args; a13; a14; a15; a16; a17]
       (bv_add (SPW args) (BV 64%N 18446744073709551520%Z)) (bv_unsigned (Z_to_bv 64 (nextUint64InputEnd args))) x.2ₗ x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hd) "? ? ?".
  ZesuSsz.Automation2.DomainRanges.zesu_pose_domain_ranges.
  ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure.
  zesu_call_slice_step.
  iFrame.
Qed.
End first_call_integer_root.

(* `zesu_split_folded_pure`: a domain with registered ranges is kept folded
   beside its conjuncts, and opened once; any other folded conjunction is
   replaced by its conjuncts. *)
Lemma split_folded_keeps_registered_domain (args : NextUint64Args) :
  nextUint64BoundaryDomain args ->
  nextUint64BoundaryDomain args /\ 112 <= ParentHeaderRootFacts.nextStackPointer (nextUint64Base args).
Proof.
  intros Hd.
  do 2 (repeat first [progress ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure |
    match goal with Hpair : _ /\ _ |- _ => destruct Hpair end]).
  lazymatch goal with
  | _ : nextUint64BoundaryDomain _ |- _ => fail
  | _ : ZesuSsz.Automation2.PureFacts.zesu_kept_domain (nextUint64BoundaryDomain _),
    _ : ZesuSsz.Automation2.PureFacts.zesu_kept_domain (nextUint64BoundaryDomain _) |- _ => fail
  | Hk : ZesuSsz.Automation2.PureFacts.zesu_kept_domain (nextUint64BoundaryDomain _) |- _ =>
      split; [exact (ZesuSsz.Automation2.PureFacts.zesu_kept_domain_elim Hk) | assumption]
  end.
Qed.

Definition call_slice_toy_folded (a b : Z) : Prop := a <= b /\ b <= a.
Lemma split_folded_opens_unregistered (a b : Z) :
  call_slice_toy_folded a b -> a = b.
Proof.
  intros Hf.
  ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure.
  Fail match goal with _ : call_slice_toy_folded _ _ |- _ => idtac end.
  lia.
Qed.

(* Early restore when the returned slice carries the callee's element type
   (`evm_rlp_types.byte`) and the lend wrote `bv 8`: matched up to
   conversion. A slice at another address is not taken. *)
Section early_restore_converted.
Context `{!islaG Sigma} `{!threadG}.
Lemma call_early_restore_converted (a b : Z) (whole : list (bv 8)) (n : nat) :
  ((b ↦ₘ∗ @take (bv 8) n whole) -∗ (a ↦ₘ∗ whole)) -∗
  (b ↦ₘ∗ @take evm_rlp_types.byte n whole) -∗
  ∃ k : Z, (a ↦ₘ∗ whole) ∗ ⌜k = 0⌝.
Proof.
  iIntros "Hr Hs".
  zesu_call_early_restore.
  iExists 0. iFrame. done.
Qed.
Lemma call_early_restore_other_address (a b c : Z) (whole : list (bv 8)) (n : nat) :
  ((b ↦ₘ∗ @take (bv 8) n whole) -∗ (a ↦ₘ∗ whole)) -∗
  (c ↦ₘ∗ @take evm_rlp_types.byte n whole) -∗
  ∃ k : Z, ((b ↦ₘ∗ @take (bv 8) n whole) -∗ (a ↦ₘ∗ whole)) ∗
    (c ↦ₘ∗ @take evm_rlp_types.byte n whole) ∗ ⌜k = 0⌝.
Proof.
  iIntros "Hr Hs".
  Fail zesu_call_early_restore.
  iExists 0. iFrame. done.
Qed.
End early_restore_converted.

(* A callee that takes its slice by reference (nextUint64 from
   decodeParentHeader, `ZesuCallSliceRefCaller`): the slice words are read
   from the eight byte cells a store left (first lemma), or from a word cell
   and the byte array of a word's little-endian bytes (second lemma); the
   window is the previous decodeItem call's window advanced by its consumed
   count; the 16-byte output slot is cut out of an uninitialised region at
   distance 0 (first lemma) and 8 (second lemma). *)
Section by_reference.
Context `{!islaG Sigma} `{!threadG}.
Notation W24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation OUT args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551320%Z)) (only parsing).
Notation NOUT args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551360%Z)) (only parsing).
Notation REF args := (bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551264%Z)) (only parsing).
Notation SP args := (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (only parsing).
Notation CELLS a w :=
  (((a + Z.of_nat 0 * 1) ↦ₘ bv_extract 0 8 w ∗ (a + Z.of_nat 1 * 1) ↦ₘ bv_extract 8 8 w ∗
    (a + Z.of_nat 2 * 1) ↦ₘ bv_extract 16 8 w ∗ (a + Z.of_nat 3 * 1) ↦ₘ bv_extract 24 8 w ∗
    (a + Z.of_nat 4 * 1) ↦ₘ bv_extract 32 8 w ∗ (a + Z.of_nat 5 * 1) ↦ₘ bv_extract 40 8 w ∗
    (a + Z.of_nat 6 * 1) ↦ₘ bv_extract 48 8 w ∗ (a + Z.of_nat 7 * 1) ↦ₘ bv_extract 56 8 w ∗
    emp)%I) (only parsing).

Lemma call_slice_by_reference_cells (args : ParentHeaderArgs) (x19 x18 : bv 64)
    (after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned x19)%Z ->
  (bv_unsigned x19 + bv_unsigned x18 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  length after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) (bv_add x19 (W24 after)) -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 8) (bv_sub x18 (W24 after)) -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56) ↦ₘ∗ after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56 + 40) ↦ₘ? 136 -∗
  R -∗
  ∃ x : list byte *ₗ bv 64 *ₗ bv 64 *ₗ (),
    bv_unsigned (REF args) ↦ₘ x.3ₗ ∗
    (bv_unsigned (REF args) + 8) ↦ₘ x.2ₗ ∗
    bv_unsigned x.3ₗ ↦ₘ∗ x.1ₗ ∗
    bv_unsigned (NOUT args) ↦ₘ? 16 ∗
    ⌜Z.of_nat (length x.1ₗ) = bv_unsigned x.2ₗ⌝ ∗
    ⌜nextUint64CallDomain (nextUint64CallDataArgs [NOUT args; REF args; bv_sub x18 (W24 after); a13; a14; a15; a16; a17]
       (SP args) x.3ₗ (parentHeaderInputEnd args) x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlo Hhi Hlen Hdom Hmean) "? ? ? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

Lemma call_slice_by_reference_words (args : ParentHeaderArgs) (x19 x18 : bv 64)
    (after : DecodeItemOutcome) (before0 : list byte)
    (a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned x19)%Z ->
  (bv_unsigned x19 + bv_unsigned x18 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  length after = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning (decodeItemCallDataArgs [OUT args; x19; x18; b13; b14; b15; b16; b17]
     (SP args) (bv_unsigned (parentHeaderInputEnd args))
     (take (Z.to_nat (bv_unsigned x18)) (drop (Z.to_nat (bv_unsigned x19 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) before0) after ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) ↦ₘ bv_add x19 (W24 after) -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 56) ↦ₘ∗
    [bv_extract 0 8 (bv_sub x18 (W24 after)); bv_extract 8 8 (bv_sub x18 (W24 after));
     bv_extract 16 8 (bv_sub x18 (W24 after)); bv_extract 24 8 (bv_sub x18 (W24 after));
     bv_extract 32 8 (bv_sub x18 (W24 after)); bv_extract 40 8 (bv_sub x18 (W24 after));
     bv_extract 48 8 (bv_sub x18 (W24 after)); bv_extract 56 8 (bv_sub x18 (W24 after))] -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56 + 120) ↦ₘ∗ after -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56 + 32) ↦ₘ? 88 -∗
  R -∗
  ∃ x : list byte *ₗ bv 64 *ₗ bv 64 *ₗ (),
    bv_unsigned (REF args) ↦ₘ x.3ₗ ∗
    (bv_unsigned (REF args) + 8) ↦ₘ x.2ₗ ∗
    bv_unsigned x.3ₗ ↦ₘ∗ x.1ₗ ∗
    bv_unsigned (NOUT args) ↦ₘ? 16 ∗
    ⌜Z.of_nat (length x.1ₗ) = bv_unsigned x.2ₗ⌝ ∗
    ⌜nextUint64CallDomain (nextUint64CallDataArgs [NOUT args; REF args; bv_sub x18 (W24 after); a13; a14; a15; a16; a17]
       (SP args) x.3ₗ (parentHeaderInputEnd args) x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf Hlo Hhi Hlen Hdom Hmean) "? ? ? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

(* The slice is the rest the previous nextUint64 call returned
   (`ZesuCallSliceRefResult`): its words are that call's rest words, its
   window follows from the previous call's record and the stated window of
   that call's slice. Without the record no window is found and the step does
   not apply. *)
Lemma call_slice_by_reference_rest (args : ParentHeaderArgs) (p0 l0 w0 w8 : bv 64)
    (res : NextUint64Return) (argv0 : list (bv 64)) (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned p0 /\
   bv_unsigned p0 + bv_unsigned l0 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv0 (SP args) p0 (parentHeaderInputEnd args)
    (take (Z.to_nat (bv_unsigned l0)) (drop (Z.to_nat (bv_unsigned p0 - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))))) res ->
  w0 = Z_to_bv 64 (nextRestPointer res) ->
  w8 = Z_to_bv 64 (nextRestLength res) ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) w0 -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 8) w8 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56 + 40) ↦ₘ? 136 -∗
  R -∗
  ∃ x : list byte *ₗ bv 64 *ₗ bv 64 *ₗ (),
    bv_unsigned (REF args) ↦ₘ x.3ₗ ∗
    (bv_unsigned (REF args) + 8) ↦ₘ x.2ₗ ∗
    bv_unsigned x.3ₗ ↦ₘ∗ x.1ₗ ∗
    bv_unsigned (NOUT args) ↦ₘ? 16 ∗
    ⌜Z.of_nat (length x.1ₗ) = bv_unsigned x.2ₗ⌝ ∗
    ⌜nextUint64CallDomain (nextUint64CallDataArgs [NOUT args; REF args; w8; a13; a14; a15; a16; a17]
       (SP args) x.3ₗ (parentHeaderInputEnd args) x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (Hwf [Hlo Hhi] Hres Hw0 Hw8) "? ? ? ? ?".
  zesu_call_slice_step.
  iFrame.
Qed.

Goal forall (args : ParentHeaderArgs) (p0 l0 w0 w8 : bv 64)
    (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma),
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned p0 /\
   bv_unsigned p0 + bv_unsigned l0 <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (@length (bv 8) (parentHeaderInputBytes args)))%Z ->
  bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48) w0 -∗
  CELLS (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 8) w8 -∗
  (bv_unsigned (parentHeaderStackPointer args) - 400 + 48 + 56 + 40) ↦ₘ? 136 -∗
  R -∗
  ∃ x : list byte *ₗ bv 64 *ₗ bv 64 *ₗ (),
    bv_unsigned (REF args) ↦ₘ x.3ₗ ∗
    (bv_unsigned (REF args) + 8) ↦ₘ x.2ₗ ∗
    bv_unsigned x.3ₗ ↦ₘ∗ x.1ₗ ∗
    bv_unsigned (NOUT args) ↦ₘ? 16 ∗
    ⌜Z.of_nat (length x.1ₗ) = bv_unsigned x.2ₗ⌝ ∗
    ⌜nextUint64CallDomain (nextUint64CallDataArgs [NOUT args; REF args; w8; a13; a14; a15; a16; a17]
       (SP args) x.3ₗ (parentHeaderInputEnd args) x.1ₗ)⌝ ∗
    R.
Proof.
  iIntros (args p0 l0 w0 w8 a13 a14 a15 a16 a17 R Hwf [Hlo Hhi]) "? ? ? ? ?".
  Fail zesu_call_slice_step.
Abort.
End by_reference.

Print Assumptions call_slice_window_advanced.
Print Assumptions call_slice_first_call_integer_root.
