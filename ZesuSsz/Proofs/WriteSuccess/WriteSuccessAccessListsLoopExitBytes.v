From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Lemma write_success_access_lists_exit_remaining_nil
    (processed remaining : list writeSuccessAccessEntry)
    (Hbound : (length (processed ++ remaining) < 2 ^ 64)%nat)
    (Heq : Z_to_bv 64 (Z.of_nat (length processed)) =
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  remaining = [].
Proof.
  have HprocessedLe :
      (length processed <= length (processed ++ remaining))%nat.
  { rewrite app_length. lia. }
  have HprocessedBound : (length processed < 2 ^ 64)%nat.
  { exact (Nat.le_lt_trans _ _ _ HprocessedLe Hbound). }
  have HprocessedRange :
      (0 <= Z.of_nat (length processed) < bv_modulus 64)%Z.
  { split; [lia |].
    change (Z.of_nat (length processed) < 2 ^ 64)%Z.
    have Hz := (proj1 (Nat2Z.inj_lt _ _) HprocessedBound).
    rewrite Nat2Z.inj_pow in Hz. exact Hz. }
  have HtotalRange :
      (0 <= Z.of_nat (length (processed ++ remaining)) < bv_modulus 64)%Z.
  { split; [lia |].
    change (Z.of_nat (length (processed ++ remaining)) < 2 ^ 64)%Z.
    have Hz := (proj1 (Nat2Z.inj_lt _ _) Hbound).
    rewrite Nat2Z.inj_pow in Hz. exact Hz. }
  have Hunsigned := f_equal bv_unsigned Heq.
  rewrite !Z_to_bv_unsigned in Hunsigned.
  rewrite !bv_wrap_small in Hunsigned; [|exact HtotalRange|exact HprocessedRange].
  have HremainingLength : length remaining = 0%nat.
  { rewrite app_length in Hunsigned. lia. }
  exact (proj1 (length_zero_iff_nil remaining) HremainingLength).
Qed.

Lemma write_success_access_lists_exit_bytes
    (processed remaining : list writeSuccessAccessEntry)
    (Hbound : (length (processed ++ remaining) < 2 ^ 64)%nat)
    (Heq : Z_to_bv 64 (Z.of_nat (length processed)) =
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  writeSuccessAccessEntriesBytes processed =
    writeSuccessAccessEntriesBytes (processed ++ remaining).
Proof.
  rewrite (write_success_access_lists_exit_remaining_nil
    processed remaining Hbound Heq).
  rewrite app_nil_r. reflexivity.
Qed.
