From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The edge of decodeParentHeader 04a8 into the error join 0270, cut to its
   frame: the successor asks for 16 uninitialized bytes where the block holds
   two word cells, then for an array the block holds, then for one 176-byte
   uninitialized region where the block holds two arrays and 120
   uninitialized bytes. The cells cover the first request exactly; its empty
   rest takes nothing (UninitRegions.subsume_uninit_empty_request), so the
   array after it stays for the second request. Without the rule the lookup
   of the empty rest found that array and weakened it: `40 <= 0`. *)
Lemma test_uninit_empty_request_frame `{!islaG Sigma} (base : Z) (w0 w1 : bv 64)
    (c10 c16 nrb : list (bv 8)) :
  length c10 = 40%nat -> length c16 = 40%nat -> length nrb = 16%nat ->
  0 <= base -> base + 400 < 2 ^ 64 ->
  (base + 48) ↦ₘ w0 -∗ (base + 48 + 8) ↦ₘ w1 -∗
  (base + 48 + 16) ↦ₘ∗ c10 -∗ (base + 48 + 56) ↦ₘ∗ c16 -∗
  (base + 48 + 56 + 40) ↦ₘ∗ nrb -∗ (base + 48 + 56 + 40 + 16) ↦ₘ? 120 -∗
  ((base + 48) ↦ₘ? 16 ∗ (base + 48 + 16) ↦ₘ∗ c10 ∗ (base + 48 + 56) ↦ₘ? 176 ∗ True).
Proof.
  intros H1 H2 H3 Hb Hb2. iStartProof.
  iIntros "H0 H1 H2 H3 H4 H5".
  liARun.
  Unshelve. all: prepare_sidecond; lia.
Qed.

Print Assumptions test_uninit_empty_request_frame.

(* The rule's guard: a size spelled from literals that computes to zero. *)
Lemma test_uninit_empty_request_guard (n : Z) : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize
    (16 - 8 - Z.of_N (64 `div` 8))) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize
    (16 - 8)) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize
    (n - n)) in idtac.
  exact I.
Qed.

(* The room guard of the array rules: refused when literal sizes show the
   request has no room for the array; symbolic sizes keep the rule. *)
Lemma test_uninit_room_guard (n : Z) : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom 40 176) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom 40 n) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom n 16) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom 40 0) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom 40 (16 - 8)) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuUninitRoom n (16 - 8 - 8)) in idtac.
  exact I.
Qed.

(* A gap: the cell covers the first 8 bytes of a 56-byte request and the
   array starts 8 bytes later. The run does not cover the gap and leaves no
   false arithmetic goal behind: the array rule is not reached for the rest
   at the gap, and an empty or short rest refuses it. *)
Lemma test_uninit_gap_refused `{!islaG Sigma} (base : Z) (w0 : bv 64) (c : list (bv 8)) :
  length c = 40%nat -> 0 <= base -> base + 400 < 2 ^ 64 -> True.
Proof.
  intros H1 Hb Hb2.
  Fail assert (⊢ base ↦ₘ w0 -∗ (base + 16) ↦ₘ∗ c -∗ (base ↦ₘ? 56 ∗ True)) by
    (iStartProof; iIntros "H0 H1"; liARun; done).
  exact I.
Qed.
