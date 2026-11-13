Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Bounds of a cursor whose base another function returned: folded, so only
   the cursor rule's fact exposure opens them. *)
Definition CallerBounds (input : Z) (bytes : list (bv 8)) (base limit : bv 64) : Prop :=
  input <= bv_unsigned base /\
  bv_unsigned (base + limit)%bv <= input + Z.of_nat (length bytes).

Definition test_goal `{!islaG Sigma} `{!threadG} : Prop := forall (input : Z) (bytes : list (bv 8))
    (cursor base limit : bv 64) (i : Z),
  CallerBounds input bytes base limit ->
  bv_unsigned cursor = bv_unsigned base + i -> 0 <= i ->
  bv_unsigned cursor < bv_unsigned (base + limit)%bv ->
  ⊢ input ↦ₘ∗ bytes -∗ find_in_context (FindMemMapsTo (bv_unsigned cursor)) (fun _ => True)%I.

(* A load at a loop cursor inside an owned array that the cursor equation does
   not name. *)
Lemma callee_bounded_cursor_lookup `{!islaG Sigma} `{!threadG} : test_goal.
Proof. unfold test_goal. intros. iIntros "Harray". zesu_block2. Qed.
