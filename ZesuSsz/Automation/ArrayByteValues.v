Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayCursors.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma array_byte_lookup (bytes : list (bv 8)) (index : nat) (byte : bv 8) :
  bytes !! index = Some byte ->
  bv_zero_extend 64 byte =
    Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop index bytes))).
Proof.
  intros Hlookup.
  have Hhead : drop index bytes !! 0%nat = Some byte.
  { rewrite lookup_drop Nat.add_0_r. exact Hlookup. }
  destruct (drop index bytes) as [|head rest] eqn:Hdrop; simpl in Hhead;
    inversion Hhead; subst.
  cbn. bv_solve.
Qed.

Lemma array_byte_pair (low high : bv 8) :
  bv_or (bv_shiftl (bv_zero_extend 64 high) (BV 64 8))
    (bv_zero_extend 64 low) =
  Z_to_bv 64 (little_endian_to_bv 8 [low; high]).
Proof.
  unfold little_endian_to_bv, little_endian_to_Z.
  rewrite !fmap_cons. cbn.
  apply bv_eq. bv_simplify. bitblast as index.
  all: (f_equal; lia).
Qed.

Lemma array_byte_pair_value (low high : bv 8) :
  bv_or (Z_to_bv 64 (bv_unsigned high * 256)) (bv_zero_extend 64 low) =
    Z_to_bv 64 (bv_unsigned low + bv_unsigned high * 256).
Proof.
  have Hshift : Z_to_bv 64 (bv_unsigned high * 256) =
      bv_shiftl (bv_zero_extend 64 high) (BV 64 8) by bv_solve.
  rewrite Hshift array_byte_pair.
  unfold little_endian_to_bv, little_endian_to_Z.
  rewrite !fmap_cons. cbn.
  rewrite Z.shiftl_0_l Z.lor_0_r.
  have Hland : Z.land (bv_unsigned low) (Z.shiftl (bv_unsigned high) 8) = 0.
  { bitblast as index. all: (f_equal; lia). }
  rewrite -Z.add_nocarry_lor //.
  rewrite Z.shiftl_mul_pow2; [|lia]. cbn. reflexivity.
Qed.
Lemma array_byte_pair_value16 (low high : bv 8) :
  bv_or (Z_to_bv 64 (bv_unsigned high * 16777216))
    (Z_to_bv 64 (bv_unsigned low * 65536)) =
  Z_to_bv 64 (bv_unsigned low * 65536 + bv_unsigned high * 16777216).
Proof.
  have Hlow : bv_unsigned low * 65536 = Z.shiftl (bv_unsigned low) 16.
  { rewrite Z.shiftl_mul_pow2; [|lia]. cbn. reflexivity. }
  have Hhigh : bv_unsigned high * 16777216 = Z.shiftl (bv_unsigned high) 24.
  { rewrite Z.shiftl_mul_pow2; [|lia]. cbn. reflexivity. }
  have Hland : Z.land (bv_unsigned low * 65536)
      (bv_unsigned high * 16777216) = 0.
  { rewrite Hlow Hhigh. bitblast as index. all: (f_equal; lia). }
  rewrite (Z.add_nocarry_lor _ _ Hland).
  apply bv_eq. bv_simplify.
  rewrite -(Z.add_nocarry_lor _ _ Hland).
  rewrite !bv_wrap_small.
  - rewrite Z.lor_comm -(Z.add_nocarry_lor _ _ Hland). reflexivity.
  - bv_saturate; unfold bv_modulus in *; cbn in *; lia.
  - bv_saturate; unfold bv_modulus in *; cbn in *; lia.
  - bv_saturate; unfold bv_modulus in *; cbn in *; lia.
Qed.

Lemma array_byte_four_value (a b c d : bv 8) :
  bv_or (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216))
    (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) =
  Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d]).
Proof.
  rewrite -array_byte_pair_value16 -array_byte_pair_value.
  have Hc : Z_to_bv 64 (bv_unsigned c * 65536) =
    bv_shiftl (bv_zero_extend 64 c) (BV 64 16) by bv_solve.
  have Hd : Z_to_bv 64 (bv_unsigned d * 16777216) =
    bv_shiftl (bv_zero_extend 64 d) (BV 64 24) by bv_solve.
  have Hb : Z_to_bv 64 (bv_unsigned b * 256) =
    bv_shiftl (bv_zero_extend 64 b) (BV 64 8) by bv_solve.
  rewrite Hc Hd Hb.
  unfold little_endian_to_bv, little_endian_to_Z.
  rewrite !fmap_cons. cbn.
  apply bv_eq. bv_simplify. bitblast as index.
  all: (f_equal; lia).
Qed.
Print Assumptions array_byte_four_value.

Lemma array_byte_eight (a b c d e f g h : bv 8) :
  bv_or (bv_shiftl (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) (BV 64 32))
    (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) =
  Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d;e;f;g;h]).
Proof.
  unfold little_endian_to_bv, little_endian_to_Z.
  rewrite !fmap_cons. cbn.
  apply bv_eq. bv_simplify. bitblast as index.
  all: (f_equal; lia).
Qed.
Print Assumptions array_byte_eight.

Lemma array_byte_pair_shift_value (low high : bv 8) :
  bv_or (bv_shiftl (bv_zero_extend 64 high) (BV 64 8))
    (bv_zero_extend 64 low) =
  Z_to_bv 64 (bv_unsigned low + bv_unsigned high * 256).
Proof.
  replace (bv_shiftl (bv_zero_extend 64 high) (BV 64 8))
    with (Z_to_bv 64 (bv_unsigned high * 256)) by bv_solve.
  apply array_byte_pair_value.
Qed.
Print Assumptions array_byte_pair_shift_value.

Lemma array_byte_pair_shift_value16 (low high : bv 8) :
  bv_or (bv_shiftl (bv_zero_extend 64 high) (BV 64 24))
    (bv_shiftl (bv_zero_extend 64 low) (BV 64 16)) =
  Z_to_bv 64 (bv_unsigned low * 65536 + bv_unsigned high * 16777216).
Proof.
  replace (bv_shiftl (bv_zero_extend 64 high) (BV 64 24))
    with (Z_to_bv 64 (bv_unsigned high * 16777216)) by bv_solve.
  replace (bv_shiftl (bv_zero_extend 64 low) (BV 64 16))
    with (Z_to_bv 64 (bv_unsigned low * 65536)) by bv_solve.
  apply array_byte_pair_value16.
Qed.
Print Assumptions array_byte_pair_shift_value16.

Ltac zesu_normalize_array_byte_lookups :=
  repeat match goal with
  | Hlookup : ?bytes !! Z.to_nat
      ((bv_unsigned (bv_add ?row ?offset) - ?base) `div` 1) = Some ?byte,
    Hcursor : bv_unsigned ?row = (?base + Z.of_nat ?index)%Z,
    Hlower : (0x20000000 <= ?base)%Z,
    Hupper : (?base + Z.of_nat (length ?bytes) < 0x40000000)%Z |- _ =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let count := eval vm_compute in (Z.to_nat integer) in
      let Hindex := fresh "HarrayByteIndex" in
      assert (Hindex : Z.to_nat (bv_unsigned (bv_add row offset) - base) =
        (index + count)%nat) by
        (eapply array_cursor_index;
          [exact Hcursor | vm_compute; reflexivity | exact Hlower |
           exact Hupper | lia]);
      rewrite Z.div_1_r Hindex in Hlookup; clear Hindex
  end.

Ltac zesu_array_byte_value :=
  zesu_normalize_array_byte_lookups;
  eapply array_byte_lookup; eassumption.
