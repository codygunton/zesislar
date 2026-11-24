Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* The exact residual tier (`zesu_residual_exact`), the registration of the
   relocatable residual modules ZesuSsz/Residuals/<function>/Block<offset>.v.

   The shape that made blocks of keysEnsureCapacity 10x slower with their
   residual lemmas registered by `Hint Resolve`: a lemma that concludes a
   negation, whose premises include implications and a variable that only
   the premises mention, beside goals the lemma has nothing to do with. Here
   such a lemma applies only to its own conclusion; an unrelated goal (a
   `False` goal among them) fails at once, whatever the context holds. *)
Lemma residual_exactTier_0000_0000000000000001 :
  forall (x : Z) (y : Z) (H0 : x <> 0 -> 0 <= y) (H1 : 0 < x) (H2 : y < 10), x * 32 <> 0.
Proof. intros; lia. Qed.
#[local] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_exactTier_0000_0000000000000001) : zesu_residual_exact.

Lemma residual_exactTier_0000_0000000000000002 :
  forall (x : Z) (y : Z) (H0 : x <> 0 -> 0 <= y) (H1 : 0 < x) (H2 : y < 10), x < x + 1 + y.
Proof. intros; lia. Qed.
#[local] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_exactTier_0000_0000000000000002) : zesu_residual_exact.

(* The conclusion fixes x; y is the context variable of the same name; each
   premise is a hypothesis. *)
Lemma residual_exact_negation_closes (a y : Z) (H0 : a <> 0 -> 0 <= y) (H1 : 0 < a) (H2 : y < 10) :
  a * 32 <> 0.
Proof. ResidualLemmas.zesu_residual_lemma. Qed.

Lemma residual_exact_lt_closes (a y : Z) (H0 : a <> 0 -> 0 <= y) (H1 : 0 < a) (H2 : y < 10) :
  a < a + 1 + y.
Proof. ResidualLemmas.zesu_residual_lemma. Qed.

(* A `False` goal whose context would let the negation lemma refute it: the
   lemma concludes `~ P`, not `False`, so it is not tried. *)
Lemma residual_exact_negation_not_on_false (a y : Z) (H0 : a <> 0 -> 0 <= y) (H1 : 0 < a)
    (H2 : y < 10) (H3 : a * 32 = 0) : False.
Proof. Fail ResidualLemmas.zesu_residual_lemma. lia. Qed.

(* Many implications in the context and an unrelated goal: no lemma's
   conclusion matches, so nothing is applied and nothing is searched. *)
Lemma residual_exact_unrelated_goal (a b c d y : Z)
    (H0 : a <> 0 -> 0 <= y) (H1 : 0 < a) (H2 : y < 10)
    (I0 : b <> 0 -> c <> 0 -> d <> 0 -> a <> 0) (I1 : c * 32 <> 0 -> b * 32 <> 0)
    (I2 : (d <> 0 -> False) -> a * 32 <> 0) (I3 : ~ (b * 32 = 0) -> ~ (c * 32 = 0))
    (H3 : a * 32 = 0) : c * 32 = 0 -> False.
Proof. Fail ResidualLemmas.zesu_residual_lemma. lia. Qed.

(* The conclusion matches but a premise is not a hypothesis: the lemma
   fails; no other way to prove the premise is tried. *)
Lemma residual_exact_missing_premise (a y : Z) (H0 : a <> 0 -> 0 <= y) (H1 : 0 < a) (H2 : y < 11) :
  a * 32 <> 0.
Proof. Fail ResidualLemmas.zesu_residual_lemma. lia. Qed.

(* A variable that only premises mention must be the context variable of
   the same name. *)
Lemma residual_exact_renamed_variable (a w : Z) (H0 : a <> 0 -> 0 <= w) (H1 : 0 < a) (H2 : w < 10) :
  a * 32 <> 0.
Proof. Fail ResidualLemmas.zesu_residual_lemma. lia. Qed.

(* Local definitions in the conclusion and in a premise: the conclusion is
   unfolded for the second try, and the premise matches by `assumption`. *)
Lemma residual_exact_local_definitions (a y : Z) :
  let b := a in (b <> 0 -> 0 <= y) -> 0 < a -> y < 10 -> b * 32 <> 0.
Proof. intros b H0 H1 H2. ResidualLemmas.zesu_residual_lemma. Qed.
