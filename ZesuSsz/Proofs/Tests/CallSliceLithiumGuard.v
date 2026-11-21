Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.NextUint64CallSlice.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* `GoalShape.zesu_call_slice_goal_unheld`, the guard in front of `liStep` in
   `Hooks.zesu_liAStep`: it fires at a callee call spec's existential whose
   input slice is not held as an array spelled the same way (nextUint64's call
   to decodeItem, block 0000), so Lithium's failing search is skipped; it does
   not fire when the slice is held, at a literal or let-bound environment
   alike, nor at an existential that is not a call spec. *)

Section guard.
Context `{!islaG Sigma} `{!threadG}.
Notation SPW args := (Z_to_bv 64 (ParentHeaderRootFacts.nextStackPointer (nextUint64Base args))) (only parsing).
Notation OUTW args := (bv_add (bv_add (bv_add (SPW args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 96%Z)) (BV 64%N 18446744073709551528%Z)) (only parsing).
Notation IPW args := (Z_to_bv 64 (ParentHeaderRootFacts.nextInputPointer (nextUint64Base args))) (only parsing).
Notation ILW args := (Z_to_bv 64 (Z.of_nat (length (ParentHeaderRootFacts.nextInputBytes (nextUint64Base args))))) (only parsing).

(* The input array is held at the integer root, the call asks for it at the
   cast word: the guard fires (literal and let-bound environment), and the
   call-site step still takes the existential. *)
Lemma call_slice_guard_fires (args : NextUint64Args) (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma) :
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
  zesu_call_slice_goal_unheld.
  let_bind_envs.
  lazymatch goal with |- environments.envs_entails ?e _ => is_var e end.
  zesu_call_slice_goal_unheld.
  ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias.
  ZesuSsz.Automation2.DomainRanges.zesu_pose_domain_ranges.
  ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure.
  zesu_call_slice_step.
  iFrame.
Qed.

(* The same call with the input array held at the address the call asks for:
   Lithium's step may take it, the guard does not fire (literal and let-bound
   environment). *)
Lemma call_slice_guard_held : True.
Proof.
  assert_succeeds (
    assert (forall (args : NextUint64Args) (a13 a14 a15 a16 a17 : bv 64) (R : iProp Sigma),
      nextUint64BoundaryDomain args ->
      bv_unsigned (IPW args) ↦ₘ∗ ParentHeaderRootFacts.nextInputBytes (nextUint64Base args) -∗
      (ParentHeaderRootFacts.nextStackPointer (nextUint64Base args) - 96) ↦ₘ? 48 -∗
      R -∗
      ∃ x : list byte *ₗ list byte *ₗ (),
        bv_unsigned (IPW args) ↦ₘ∗ x.2ₗ ∗
        bv_unsigned (OUTW args) ↦ₘ∗ x.1ₗ ∗
        ⌜decodeItemCallDomain (decodeItemCallDataArgs [OUTW args; IPW args; ILW args; a13; a14; a15; a16; a17]
           (bv_add (SPW args) (BV 64%N 18446744073709551520%Z)) (bv_unsigned (Z_to_bv 64 (nextUint64InputEnd args))) x.2ₗ x.1ₗ)⌝ ∗
        R) as _;
    [ intros args a13 a14 a15 a16 a17 R Hd; iIntros "? ? ?";
      tryif zesu_call_slice_goal_unheld then fail else idtac;
      let_bind_envs;
      lazymatch goal with |- environments.envs_entails ?e _ => is_var e end;
      tryif zesu_call_slice_goal_unheld then fail else idtac
    | ]).
  exact I.
Qed.
End guard.

(* An existential over a list pair that is not a call spec: no guard. *)
Section not_a_call.
Context `{!islaG Sigma} `{!threadG}.
Lemma call_slice_guard_not_a_call (base : Z) (bytes : list (bv 8)) (tail : spec) :
  length bytes = 592%nat ->
  base ↦ₘ∗ bytes -∗ spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    (base + 152)%Z ↦ₘ∗ x.2ₗ ∗ spec_trace x.1ₗ ∗
    ⌜32%Z = Z.of_nat (length x.2ₗ)⌝ ∗
    ((base + 152)%Z ↦ₘ∗ x.2ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hlength) "Harray Htrace".
  Fail zesu_call_slice_goal_unheld.
  ZesuSsz.Automation2.InteriorByteSlice.zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  rewrite length_take length_drop. lia.
Qed.
End not_a_call.
