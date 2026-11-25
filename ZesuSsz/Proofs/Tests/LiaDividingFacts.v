From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.LinearFirstLia.
Require Import ZesuSsz.Automation2.All.
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

(* The linked-facts solver refuses a goal with more than 24 distinct
   remainders, even one it would prove (the goal closes by reflexivity once
   the solver has refused); with few it runs (the unrelated fact is cleared
   first). *)
Lemma linked_facts_many_remainders (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
    x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 z : Z) :
  z = 1 ->
  x0 mod 3 + x1 mod 3 + x2 mod 3 + x3 mod 3 + x4 mod 3 + x5 mod 3 + x6 mod 3 +
    x7 mod 3 + x8 mod 3 + x9 mod 3 + x10 mod 3 + x11 mod 3 + x12 mod 3 + x13 mod 3 +
    x14 mod 3 + x15 mod 3 + x16 mod 3 + x17 mod 3 + x18 mod 3 + x19 mod 3 + x20 mod 3 +
    x21 mod 3 + x22 mod 3 + x23 mod 3 + x24 mod 3 =
  x0 mod 3 + x1 mod 3 + x2 mod 3 + x3 mod 3 + x4 mod 3 + x5 mod 3 + x6 mod 3 +
    x7 mod 3 + x8 mod 3 + x9 mod 3 + x10 mod 3 + x11 mod 3 + x12 mod 3 + x13 mod 3 +
    x14 mod 3 + x15 mod 3 + x16 mod 3 + x17 mod 3 + x18 mod 3 + x19 mod 3 + x20 mod 3 +
    x21 mod 3 + x22 mod 3 + x23 mod 3 + x24 mod 3.
Proof.
  intros Hz.
  Fail zesu_lia_linked_facts.
  reflexivity.
Qed.

Lemma linked_facts_few_remainders (x y z : Z) :
  z = 1 -> x mod 3 + y mod 5 = y mod 5 + x mod 3.
Proof.
  intros Hz. zesu_lia_linked_facts.
Qed.
