Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Local Open Scope Z_scope.

Lemma finish_defer_word (base : Z) :
  (Z_to_bv 64 (base - 16) + 16)%bv = Z_to_bv 64 base.
Proof.
  ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  bv_solve.
Qed.

Lemma finish_defer_length (base : Z) (values : list (bv 8))
    (Hlength : length values = 16%nat) (Hupper : base < 2^64) :
  base - 16 + Z.of_nat (length values) <= 2^64.
Proof.
  ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  rewrite Hlength. lia.
Qed.

Local Definition finish_defer_amount : Z := 16.
Local Definition finish_defer_limit : Z := 2^64.

Lemma finish_defer_closed_word (base : Z) :
  (Z_to_bv 64 (base - finish_defer_amount) + 16)%bv = Z_to_bv 64 base.
Proof.
  ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  unfold finish_defer_amount. bv_solve.
Qed.

Lemma finish_defer_closed_limit (base : Z) (values : list (bv 8))
    (Hlength : length values = 16%nat) (Hupper : base <= finish_defer_limit) :
  base - 16 + Z.of_nat (length values) <= 2^64.
Proof.
  ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  unfold finish_defer_limit in Hupper. rewrite Hlength. lia.
Qed.

Lemma finish_defer_word_evar : exists base : Z,
  (Z_to_bv 64 (base - 16) + 16)%bv = Z_to_bv 64 base.
Proof.
  eexists.
  Show Existentials.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  lazymatch goal with |- ?target => has_evar target end.
  Show Existentials.
  lazymatch goal with
  | |- @eq (bv _) _ (Z_to_bv _ ?witness) =>
      is_evar witness; unify witness 0%Z
  end.
  bv_solve.
Qed.

Lemma finish_defer_length_evar : forall (base : Z) (values : list (bv 8)),
  length values = 16%nat -> base < 2^64 ->
  exists witness : Z, witness - 16 + Z.of_nat (length values) <= 2^64.
Proof.
  intros base values Hlength Hupper. eexists.
  Show Existentials.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  lazymatch goal with |- ?target => has_evar target end.
  Show Existentials.
  lazymatch goal with
  | |- Z.le (Z.add (Z.sub ?witness _) _) _ =>
      is_evar witness; unify witness base
  end.
  rewrite Hlength. lia.
Qed.

Lemma finish_defer_symbolic_fallback (base limit : Z) (values : list (bv 8))
    (Hlength : length values = 16%nat) (Hupper : base < limit) :
  base - 16 + Z.of_nat (length values) <= limit.
Proof.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  tryif ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape
  then idtac else bv_solve.
Qed.

Lemma finish_defer_unequal_fallback (base : Z) (values : list (bv 8))
    (Hlength : length values = 16%nat) (Hupper : base < 64) :
  base - 16 + Z.of_nat (length values) <= 128.
Proof.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  tryif ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape
  then idtac else bv_solve.
Qed.

Lemma finish_defer_missing_length (base : Z) (values : list (bv 8))
    (Hupper : base < 2^64)
    (Hgoal : base - 16 + Z.of_nat (length values) <= 2^64) :
  base - 16 + Z.of_nat (length values) <= 2^64.
Proof.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  exact Hgoal.
Qed.

Lemma finish_defer_missing_upper (base : Z) (values : list (bv 8))
    (Hlength : length values = 16%nat)
    (Hgoal : base - 16 + Z.of_nat (length values) <= 2^64) :
  base - 16 + Z.of_nat (length values) <= 2^64.
Proof.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  exact Hgoal.
Qed.

Lemma finish_defer_symbolic_amount (base amount : Z)
    (Hgoal : (Z_to_bv 64 (base - amount) + 16)%bv = Z_to_bv 64 base) :
  (Z_to_bv 64 (base - amount) + 16)%bv = Z_to_bv 64 base.
Proof.
  Fail ZesuSsz.Automation.Finish.zesu_finish_defer_cancel_shape.
  exact Hgoal.
Qed.

Print Assumptions finish_defer_word.
Print Assumptions finish_defer_length.
Print Assumptions finish_defer_closed_word.
Print Assumptions finish_defer_closed_limit.
Print Assumptions finish_defer_symbolic_fallback.
Print Assumptions finish_defer_unequal_fallback.
Print Assumptions finish_defer_word_evar.
Print Assumptions finish_defer_length_evar.
Print Assumptions finish_defer_missing_length.
Print Assumptions finish_defer_missing_upper.
Print Assumptions finish_defer_symbolic_amount.
