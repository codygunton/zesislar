Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The cascade's closers skip a goal that holds open existential witnesses. *)
Lemma open_witnesses_detected `{!islaG Sigma} `{!threadG} (R : iProp Sigma) :
  R -∗ ∃ w : bv 64, ⌜(bv_unsigned w < 3)%Z⌝ ∗ R.
Proof.
  iIntros "HR".
  ZesuSsz.Automation2.Finish.zesu_goal_holds_open_witnesses.
  iExists (BV 64 0). iFrame. iPureIntro. vm_compute. reflexivity.
Qed.

Lemma closed_goal_not_detected (x : Z) : (x < 5)%Z -> (x < 10)%Z.
Proof.
  intros Hx.
  Fail ZesuSsz.Automation2.Finish.zesu_goal_holds_open_witnesses.
  lia.
Qed.

(* Cost fixture: an open package with 26 existential witnesses whose pure
   conjuncts cannot close. The sentence time is the cost of the failing
   end-of-block steps. *)
Lemma open_package_that_cannot_close `{!islaG Sigma} `{!threadG} : True.
Proof.
  Fail assert (Hopen : forall (a : bv 64) (R : iProp Sigma),
    R -∗ ∃ (w0 : bv 64) (w1 : bv 64) (w2 : bv 64) (w3 : bv 64) (w4 : bv 64) (w5 : bv 64) (w6 : bv 64) (w7 : bv 64) (w8 : bv 64) (w9 : bv 64) (w10 : bv 64) (w11 : bv 64) (w12 : bv 64) (w13 : bv 64) (w14 : bv 64) (w15 : bv 64) (w16 : bv 64) (w17 : bv 64) (w18 : bv 64) (w19 : bv 64) (w20 : bv 64) (w21 : bv 64) (w22 : bv 64) (w23 : bv 64) (w24 : bv 64) (w25 : bv 64), ⌜(bv_unsigned w0 + 0 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w1 + 1 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w2 + 2 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w3 + 3 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w4 + 4 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w5 + 5 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w6 + 6 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w7 + 7 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w8 + 8 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w9 + 9 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w10 + 10 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w11 + 11 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w12 + 12 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w13 + 13 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w14 + 14 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w15 + 15 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w16 + 16 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w17 + 17 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w18 + 18 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w19 + 19 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w20 + 20 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w21 + 21 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w22 + 22 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w23 + 23 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w24 + 24 < bv_unsigned a)%Z⌝ ∗ ⌜(bv_unsigned w25 + 25 < bv_unsigned a)%Z⌝ ∗ R) by (intros a R; iIntros "HR"; zesu_block2).
  exact I.
Qed.
