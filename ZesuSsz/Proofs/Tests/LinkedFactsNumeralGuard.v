Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith Lia List.
Import ListNotations.
Local Open Scope Z_scope.

(* berlinGasCalc 3f00: the range fact of a saved-flag array whose bytes divide
   by `2 ^ Z.of_N 128`. `Zify.zify` pulls those divisions out of the list and
   `xlia` grew to 8 GiB on the block; the linked-facts closer refuses. The
   closer runs only when it clears a fact (`Hother`). *)
Lemma linked_facts_symbolic_divisor (sp a x y : Z) :
  0 <= a /\ a + Z.of_N 1 * Z.of_nat (length
    [x `div` 2 ^ Z.of_N 128; x `mod` 2 ^ Z.of_N 128; (x + 1) `div` 2 ^ Z.of_N 128]) <= 2 ^ 64 ->
  a = sp - 40 + 24 -> y = 3 ->
  sp - 40 + 24 <= 2 ^ 64.
Proof.
  intros Hrange Ha Hother.
  Fail ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linked_facts.
  destruct Hrange as [_ Hrange]. subst a.
  pose proof (Zle_0_nat (length
    [x `div` 2 ^ Z.of_N 128; x `mod` 2 ^ Z.of_N 128; (x + 1) `div` 2 ^ Z.of_N 128])).
  change (Z.of_N 1) with 1 in Hrange.
  Zify.zify; xlia Lia.zchecker.
Qed.

(* A divisor `2 ^ (8 * Z.of_nat 7)` (nextUint64 00b8) is refused too. *)
Lemma linked_facts_symbolic_power (a x y : Z) :
  a + Z.of_nat (length [x `div` 2 ^ (8 * Z.of_nat 7)]) <= 10 -> y = 3 -> a <= 10.
Proof.
  intros Hrange Hother.
  Fail ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linked_facts.
  pose proof (Zle_0_nat (length [x `div` 2 ^ (8 * Z.of_nat 7)])).
  Zify.zify; xlia Lia.zchecker.
Qed.

(* A power of two numerals counts as a numeral: the bitvector modulus. *)
Lemma linked_facts_modulus_numeral (sp a w y : Z) :
  a = w mod 2 ^ 64 -> sp = a + 8 -> y = 3 -> 8 <= sp.
Proof.
  intros Ha Hsp Hother.
  ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linked_facts.
Qed.
