From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Automation2.LinearFirstLia.
Local Open Scope Z_scope.

(* The whole-context arm of the project lia reads no dividing fact on a goal
   that does not divide (LinearFirstLia.zesu_lia_clear_dividing_facts). *)
Lemma dividing_facts_cleared (x y : Z) :
  x mod 16 = 0 -> (8 | y) -> x <= 3 -> x <= 5.
Proof.
  intros Hmod Hdiv Hle.
  zesu_lia_clear_dividing_facts.
  Fail match goal with H : _ mod _ = _ |- _ => idtac end.
  Fail match goal with H : (_ | _) |- _ => idtac end.
  lia.
Qed.

(* A goal that divides keeps them. *)
Lemma dividing_facts_kept (x : Z) :
  x mod 16 = 0 -> (x + 32) mod 16 = 0.
Proof.
  intros Hmod.
  zesu_lia_clear_dividing_facts.
  match goal with H : _ mod _ = _ |- _ => idtac end.
  rewrite Z.add_mod by lia. rewrite Hmod. reflexivity.
Qed.
