Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma access_copy_processed_values {A} (base : Z)
    (entries processed remaining : list A) (bytes : list byte) :
  entries = processed ++ remaining -> length bytes = (40 * length entries)%nat ->
  (0x20000000 <= base)%Z -> (base + Z.of_nat (length bytes) < 0x40000000)%Z ->
  bv_unsigned (Z_to_bv 64 (Z.of_nat (length processed))) = Z.of_nat (length processed) /\
  bv_unsigned (Z_to_bv 64 base) = base.
Proof.
  intros Hsplit Hsize Hlow Hhigh.
  have Hproc : (Z.of_nat (length processed) <= Z.of_nat (length entries))%Z.
  { rewrite Hsplit app_length Nat2Z.inj_add. lia. }
  rewrite Hsize Nat2Z.inj_mul in Hhigh.
  change (base + 40 * Z.of_nat (length entries) < 1073741824)%Z in Hhigh.
  split.
  - rewrite Z_to_bv_small; [reflexivity|unfold bv_modulus; cbn; lia].
  - rewrite Z_to_bv_small; [reflexivity|unfold bv_modulus; cbn; lia].
Qed.
Print Assumptions access_copy_processed_values.

Lemma access_copy_row_bound {A} (entries processed rest : list A) (entry : A)
    (bytes : list byte) :
  entries = processed ++ entry :: rest -> length bytes = (40 * length entries)%nat ->
  (40 * length processed + 40 <= length bytes)%nat.
Proof. intros Hsplit Hsize. rewrite Hsize Hsplit app_length. simpl. lia. Qed.
Print Assumptions access_copy_row_bound.
