From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* UninitRegions.subsume_uninit_empty_region_array / _uninit
   (decodeParentHeader 0514_slot2): the lookup by address found the EMPTY
   region `a ↦ₘ? 0` for a request of 10 bytes at `a`, and the
   uninitialized-region rule raised `a + 10 <= a + 0`. The empty region is
   dropped and the request is asked again. *)
Section empty_region.
Context `{!islaG Sigma} `{!threadG}.

(* Array request of closed positive length: the search step takes the rule
   (without it, the uninitialized-request rule, whose goal holds the false
   containment), and what is left is the request itself. *)
Lemma test_empty_region_array (a : Z) (x y : bv 8) :
  ⊢ a ↦ₘ∗ [x; y] -∗ subsume (a ↦ₘ? 0) (λ _ : unit, a ↦ₘ∗ [x; y]) (λ _, True)%I.
Proof.
  iIntros "H".
  liStep.
  lazymatch goal with
  | |- context [ZesuSsz.Automation2.UninitRegions.subsume_uninit_empty_region_array_inst] => idtac
  end.
  simpl. iExists (). iFrame.
Qed.

(* Uninitialized request of closed positive size. *)
Lemma test_empty_region_uninit (a : Z) :
  ⊢ a ↦ₘ? 6 -∗ subsume (a ↦ₘ? 0) (λ _ : unit, a ↦ₘ? 6) (λ _, True)%I.
Proof.
  iIntros "H".
  liStep.
  lazymatch goal with
  | |- context [ZesuSsz.Automation2.UninitRegions.subsume_uninit_empty_region_uninit_inst] => idtac
  end.
  simpl. iExists (). iFrame.
Qed.
End empty_region.

(* Guards. The region must be closed and empty; the request closed and
   positive. *)
Lemma test_empty_region_guards (l : list (bv 8)) (n : Z) (x : bv 8) : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveRequest
    (fun _ : unit => [x; x])) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveRequest
    (fun _ : unit => l)) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveRequest
    (fun _ : unit => @nil (bv 8))) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveSize 6) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveSize 0) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedPositiveSize n) in idtac.
  (* A region that is not empty, or not closed, is not dropped. *)
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize 0) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize 2) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuClosedZeroSize n) in idtac.
  exact I.
Qed.
