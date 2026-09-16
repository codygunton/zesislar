Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Lemma access_counter_remaining_nil {A} (entries processed remaining : list A) :
  entries = processed ++ remaining -> (length entries < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length entries)) ->
  remaining = [].
Proof.
  intros Hsplit Hbound Heq.
  apply Nat2Z.inj_lt in Hbound. rewrite Nat2Z.inj_pow in Hbound.
  change (Z.of_nat (length entries) < 18446744073709551616)%Z in Hbound.
  have Hproc : (Z.of_nat (length processed) <= Z.of_nat (length entries))%Z.
  { rewrite Hsplit app_length Nat2Z.inj_add. lia. }
  have Hproc0 : (0 <= Z.of_nat (length processed))%Z by lia.
  have Hentry0 : (0 <= Z.of_nat (length entries))%Z by lia.
  have Hlength : Z.of_nat (length processed) = Z.of_nat (length entries).
  { apply (f_equal bv_unsigned) in Heq.
    rewrite !Z_to_bv_small in Heq.
    - exact Heq.
    - unfold bv_modulus. cbn. lia.
    - unfold bv_modulus. cbn. lia. }
  apply length_zero_iff_nil. rewrite Hsplit app_length in Hlength.
  rewrite Nat2Z.inj_add in Hlength. lia.
Qed.
Print Assumptions access_counter_remaining_nil.

Lemma access_counter_remaining_nonempty {A} (entries processed remaining : list A) :
  entries = processed ++ remaining ->
  Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length entries)) ->
  remaining <> [].
Proof.
  intros Hsplit Hne Hnil. subst remaining.
  rewrite app_nil_r in Hsplit. subst entries. apply Hne. reflexivity.
Qed.
Print Assumptions access_counter_remaining_nonempty.
