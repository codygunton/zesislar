Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Compliance.FreeSizeClassLeafFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma freeSizeClassIte41f7c (size : Z) :
  0 <= size <= 16 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_signed 128 (@BV 128 9 I))) then 0 else 1.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 9) then 0 else 1).
  destruct (bool_decide (size < 9)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf0. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf1. lia. }
Qed.

Lemma freeSizeClassIte42010 (size : Z) :
  262145 <= size <= 1048576 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_unsigned 64 (@BV 64 524289 I))) then 16 else 17.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 524289) then 16 else 17).
  destruct (bool_decide (size < 524289)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf16. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf17. lia. }
Qed.

Lemma freeSizeClassIte42028 (size : Z) :
  17 <= size <= 64 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_signed 128 (@BV 128 33 I))) then 2 else 3.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 33) then 2 else 3).
  destruct (bool_decide (size < 33)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf2. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf3. lia. }
Qed.

Lemma freeSizeClassIte42054 (size : Z) :
  16385 <= size <= 65536 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_unsigned 64 (@BV 64 32769 I))) then 12 else 13.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 32769) then 12 else 13).
  destruct (bool_decide (size < 32769)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf12. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf13. lia. }
Qed.

Lemma freeSizeClassIte42070 (size : Z) :
  513 <= size <= 2048 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_signed 128 (@BV 128 1025 I))) then 7 else 8.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 1025) then 7 else 8).
  destruct (bool_decide (size < 1025)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf7. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf8. lia. }
Qed.

Lemma freeSizeClassIte420b0 (size : Z) :
  4097 <= size <= 16384 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_unsigned 64 (@BV 64 8193 I))) then 10 else 11.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 8193) then 10 else 11).
  destruct (bool_decide (size < 8193)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf10. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf11. lia. }
Qed.

Lemma freeSizeClassIte420cc (size : Z) :
  129 <= size <= 512 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_signed 128 (@BV 128 257 I))) then 5 else 6.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 257) then 5 else 6).
  destruct (bool_decide (size < 257)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf5. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf6. lia. }
Qed.

Lemma freeSizeClassIte420ec (size : Z) :
  1048577 <= size <= 4194304 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_unsigned 64 (@BV 64 2097153 I))) then 18 else 19.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 2097153) then 18 else 19).
  destruct (bool_decide (size < 2097153)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf18. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf19. lia. }
Qed.

Lemma freeSizeClassIte4210c (size : Z) :
  65537 <= size <= 262144 ->
  freeSizeClassOfBytes size =
    if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (size))) (@bv_unsigned 64 (@BV 64 131073 I))) then 14 else 15.
Proof.
  intros Hrange.
  assert (Hfits : 0 <= size < bv_modulus 64).
  { change (0 <= size < 18446744073709551616). lia. }
  rewrite (Z_to_bv_small 64 size Hfits).
  change (freeSizeClassOfBytes size = if bool_decide (size < 131073) then 14 else 15).
  destruct (bool_decide (size < 131073)) eqn:Hbranch.
  { apply bool_decide_eq_true in Hbranch. apply freeSizeClassLeaf14. lia. }
  { apply bool_decide_eq_false in Hbranch. apply freeSizeClassLeaf15. lia. }
Qed.

