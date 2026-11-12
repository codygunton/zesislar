(* Tests for wrap-to-linear (ZesuSsz/Automation2/WrapLinear.v) through the
   project's lia, bv_solve and the block cache step. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions list.
From iris.proofmode Require Import proofmode.
Require Import ZesuSsz.Automation2.All.

Section wrap_linear_solver_tests.
Local Open Scope Z_scope.

(* Inside a solver call, a remainder by a divisor of 2^64 is linear with no
   range: the constant 2^64 - 96 is the centered residue -96. *)
Goal forall f : Z, 96 <= f < 2^64 -> (16 | f) ->
  bv_unsigned (bv_add (Z_to_bv 64 f) (BV 64 (2^64 - 96))) mod 16 = 0.
Proof. intros f Hf Hdivide. lia. Qed.

(* Held-out shape 2: the remainder needs only the divisibility fact. *)
Goal forall s : Z, (16 | s) ->
  bv_unsigned (bv_add (Z_to_bv 64 s) (BV 64 (2^64 - 96))) mod 16 = 0.
Proof. intros s Hdivide. lia. Qed.

(* Without a range the sum can wrap: no equation, the goal stays open. *)
Goal forall x : bv 64, bv_unsigned (bv_add x (BV 64 8)) = bv_unsigned x + 8.
Proof. intros x. Fail lia. Abort.

End wrap_linear_solver_tests.

Section wrap_linear_cache_tests.
Context {PROP : bi}.
Local Open Scope Z_scope.

(* A wrapped cast sum under the range of its integer: the cache step proves the
   range once and poses the unwrap; the solver then reads a linear term. *)
Lemma wrap_cache_cast_sum (p : Z) :
  0 <= p < 2^64 - 8 ->
  ⊢@{PROP} ⌜bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8)) <= p + 8⌝ ∗ True.
Proof.
  intros Hp. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [iPureIntro; lia | iPureIntro; exact I].
Qed.

(* A strict bound, which W1a refuses because it is not an equality. *)
Lemma wrap_cache_strict_bound (x : bv 64) :
  bv_unsigned x < 2^64 - 8 ->
  ⊢@{PROP} ⌜bv_unsigned (bv_add x (BV 64 8)) < bv_unsigned x + 16⌝ ∗ True.
Proof.
  intros Hx. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [iPureIntro; lia | iPureIntro; exact I].
Qed.

(* Held-out shape 1, store after store: the only range is the earlier store's
   signed 128-bit check, which bounds the wrapped address, not p. *)
Lemma wrap_cache_store_after_store (p m : Z) :
  bv_signed (bv_zero_extend 128 (Z_to_bv 64 p)) >= bv_signed (BV 128 4096) ->
  bv_signed (bv_add (bv_zero_extend 128 (Z_to_bv 64 p)) (BV 128 8)) <=
    bv_signed (BV 128 65536) ->
  0 < m ->
  ⊢@{PROP} ⌜((bv_unsigned (Z_to_bv 64 p) + 8 <= bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8)) <
     bv_unsigned (Z_to_bv 64 p) + 8 + m) \/
    bv_unsigned (Z_to_bv 64 p) + 8 = bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8)))%Z⌝ ∗ True.
Proof.
  intros Hlow Hhigh Hm. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [iPureIntro; bv_solve | iPureIntro; exact I].
Qed.

(* Held-out shape 1, bounded base: the signed check of an access at x + 16
   fixes the range of x through its quotient. *)
Lemma wrap_cache_bounded_base (x : bv 64) :
  bv_signed (bv_zero_extend 128 (bv_add x (BV 64 16))) >= bv_signed (BV 128 4096) ->
  bv_signed (bv_add (bv_zero_extend 128 (bv_add x (BV 64 16))) (BV 128 8)) <=
    bv_signed (BV 128 65536) ->
  ⊢@{PROP} ⌜(bv_unsigned x + 24 = bv_unsigned (bv_add x (BV 64 24)))%Z⌝ ∗ True.
Proof.
  intros Hlow Hhigh. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [iPureIntro; bv_solve | iPureIntro; exact I].
Qed.

(* 4. One step poses one equation for the shared term; a second step fails. *)
Lemma wrap_cache_step_once (x : bv 64) :
  bv_unsigned x < 2^64 - 8 ->
  ⊢@{PROP} ⌜bv_unsigned (bv_add x (BV 64 8)) <= bv_unsigned x + 8⌝ ∗
    ⌜0 < bv_unsigned (bv_add x (BV 64 8))⌝ ∗ True.
Proof.
  intros Hx. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  Fail ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  (* Exactly one equation (match goal binds distinct hypotheses). *)
  match goal with H : bv_unsigned (bv_add x _) = _ |- _ => idtac end.
  Fail match goal with
  | H1 : bv_unsigned (bv_add x _) = _, H2 : bv_unsigned (bv_add x _) = _ |- _ => idtac
  end.
  iSplitR; [iPureIntro; lia |].
  iSplitR; [iPureIntro; pose proof (bv_unsigned_in_range _ x); lia | iPureIntro; exact I].
Qed.

(* Without a range the step records a refusal and poses no equation. *)
Lemma wrap_cache_step_refuses (x : bv 64) :
  ⊢@{PROP} ⌜bv_unsigned (bv_add x (BV 64 8)) = bv_unsigned (bv_add x (BV 64 8))⌝ ∗ True.
Proof.
  iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  Fail match goal with H : bv_unsigned (bv_add x _) = _ |- _ => idtac end.
  Fail ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [by iPureIntro | iPureIntro; exact I].
Qed.

(* Held-out shape 3: the unwrap fact enters the main context at a pure head
   and serves a later goal that is not arithmetic. *)
Lemma wrap_cache_step_persists (x : Z) (bytes : list (bv 8)) :
  0 <= x < 2^63 ->
  ⊢@{PROP} ⌜0 <= bv_unsigned (bv_add (Z_to_bv 64 x) (BV 64 16))⌝ ∗
    ⌜drop (Z.to_nat (bv_unsigned (bv_add (Z_to_bv 64 x) (BV 64 16)) - x)) bytes =
      drop 16%nat bytes⌝.
Proof.
  intros Hx. iStartProof.
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  iSplitR; [iPureIntro; lia |].
  iPureIntro.
  match goal with H : bv_unsigned (bv_add (Z_to_bv 64 x) _) = x + 16 |- _ => rewrite H end.
  replace (x + 16 - x) with 16 by lia. reflexivity.
Qed.
End wrap_linear_cache_tests.

Section wrap_linear_lookup_tests.
Context `{!islaG Sigma} `{!threadG}.
Local Open Scope Z_scope.

(* Held-out shape 1 at the lookup head: the step poses the anchored unwrap in
   the main context; a later lookup side condition closes with it alone. *)
Lemma wrap_cache_lookup (p : Z) (T : mem_mapsto_kind -> iProp Sigma) :
  bv_signed (bv_zero_extend 128 (Z_to_bv 64 p)) >= bv_signed (BV 128 4096) ->
  bv_signed (bv_add (bv_zero_extend 128 (Z_to_bv 64 p)) (BV 128 8)) <=
    bv_signed (BV 128 65536) ->
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8)))) T ⊢
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8)))) T.
Proof.
  intros Hlow Hhigh. iIntros "H".
  ZesuSsz.Automation2.WrapLinear.zesu_wrap_cache_step.
  assert (Hside : bv_unsigned (Z_to_bv 64 p) + 8 =
      bv_unsigned (bv_add (Z_to_bv 64 p) (BV 64 8))) by (clear Hlow Hhigh; bv_solve).
  iExact "H".
Qed.
End wrap_linear_lookup_tests.
