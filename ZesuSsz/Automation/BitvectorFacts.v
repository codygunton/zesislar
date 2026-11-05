(* Generic bit-vector facts, moved from the writeSuccess proof tree. *)
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Automation.VmClosed.
From iris.bi Require Import interface.
Local Open Scope Z_scope.

Import ListNotations.

Lemma bv_sign_extend_64_idemp (b : bv 64) : bv_sign_extend 64 b = b.
Proof. apply bv_sign_extend_idemp. Qed.

Lemma bv_zero_extend_64_zero_8 (b : bv 8) :
  bv_zero_extend 64 b = BV 64 0 -> b = BV 8 0.
Proof.
  move => Hzero.
  apply bv_eq.
  move: (f_equal bv_unsigned Hzero).
  rewrite bv_zero_extend_unsigned // !bv_unsigned_BV //.
Qed.

Lemma bv_unsigned_add_no_wrap_64 (left right : bv 64) :
  (bv_unsigned left + bv_unsigned right < 2 ^ 64)%Z ->
  bv_unsigned (left + right)%bv = bv_unsigned left + bv_unsigned right.
Proof.
  move => Hsum. rewrite bv_add_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 left).
  pose proof (bv_unsigned_in_range 64 right).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

(* Select this rule explicitly. Unselected proofs keep their search order. *)
Class ZesuStepSignedAddress : Prop := zesu_step_signed_address : True.

Lemma zesu_signed_zero_extend_64_128 (value : bv 64) :
  bv_signed (bv_zero_extend 128 value) = bv_unsigned value.
Proof. rewrite bv_zero_extend_signed bv_swrap_small; bv_solve. Qed.

Class ZesuStepStrictSigned : Prop := zesu_step_strict_signed : True.

Lemma zesu_unsigned_lt_signed_zero_extend_64_128 (left right : bv 64) :
  bv_unsigned left < bv_unsigned right ->
  bv_signed (bv_zero_extend 128 left) <
    bv_signed (bv_zero_extend 128 right).
Proof. rewrite !zesu_signed_zero_extend_64_128. exact (fun Hlt => Hlt). Qed.

Lemma zesu_signed_zero_extend_add_64_128
    (value : bv 64) (offset : bv 128) :
  bv_unsigned offset < 2 ^ 64 ->
  bv_signed (bv_zero_extend 128 value + offset) =
    bv_unsigned value + bv_unsigned offset.
Proof.
  move => Hoffset.
  rewrite bv_add_signed bv_zero_extend_signed.
  rewrite !bv_swrap_small; bv_solve.
Qed.

Lemma zesu_unsigned_add_signed_64 (left right : bv 64) :
  0 <= bv_unsigned left + bv_signed right < 2 ^ 64 ->
  bv_unsigned (left + right) = bv_unsigned left + bv_signed right.
Proof. move => Hsum. bv_solve. Qed.

Lemma zesu_unsigned_sub_no_wrap_64 (left right : bv 64) :
  bv_unsigned right <= bv_unsigned left ->
  bv_unsigned (left - right) = bv_unsigned left - bv_unsigned right.
Proof. move => Hsub. rewrite bv_sub_unsigned bv_wrap_small; bv_solve. Qed.

Class ZesuStepLowMask : Prop := zesu_step_low_mask : True.

Class ZesuStepMaskNormalizer : Prop := zesu_step_mask_normalizer : True.

Lemma zesu_unsigned_low_mask_add (width low : N)
    (value offset mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (value + offset) mask) =
    bv_unsigned (Z_to_bv low (bv_unsigned value + bv_unsigned offset)).
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask -bv_wrap_land bv_add_unsigned Z_to_bv_unsigned.
  apply bv_wrap_bv_wrap. exact Hwidth.
Qed.

Lemma zesu_unsigned_low_mask_add_integer (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (value + Z_to_bv width offset) mask) =
    bv_unsigned (Z_to_bv low (bv_unsigned value + offset)).
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask -bv_wrap_land bv_add_unsigned !Z_to_bv_unsigned.
  rewrite (bv_wrap_bv_wrap low width _ Hwidth).
  rewrite -(bv_wrap_add_idemp_r low (bv_unsigned value) (bv_wrap width offset)).
  rewrite (bv_wrap_bv_wrap low width _ Hwidth).
  apply bv_wrap_add_idemp_r.
Qed.

Lemma zesu_unsigned_low_mask_add_sub_modulus (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value + offset < 2 * bv_modulus low ->
  bv_unsigned (bv_and (value + Z_to_bv width offset) mask) =
    bv_unsigned value + offset - bv_modulus low.
Proof.
  intros Hwidth Hmask Hrange.
  rewrite (zesu_unsigned_low_mask_add_integer width low value mask offset Hwidth Hmask).
  rewrite Z_to_bv_unsigned.
  rewrite -(bv_wrap_sub_modulus_1 low (bv_unsigned value + offset)).
  apply bv_wrap_small. lia.
Qed.


Lemma zesu_low_mask_add_bv_sub_modulus (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value + offset < 2 * bv_modulus low ->
  bv_and (value + Z_to_bv width offset) mask =
    Z_to_bv width (bv_unsigned value + offset - bv_modulus low).
Proof.
  intros Hwidth Hmask Hrange.
  apply bv_eq. rewrite bv_and_unsigned Z_to_bv_unsigned.
  pose proof (zesu_unsigned_low_mask_add_sub_modulus
    width low value mask offset Hwidth Hmask Hrange) as Hunsigned.
  rewrite bv_and_unsigned in Hunsigned. rewrite Hunsigned.
  symmetry. apply bv_wrap_small.
  pose proof (bv_modulus_le_mono low width Hwidth). lia.
Qed.

(* Normalize supported branch conditions before general arithmetic. *)
Class ZesuStepBranchGuards : Prop := zesu_step_branch_guards : True.

Lemma zesu_guard_low_mask_one_wrap (width low : N) (value mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value < 2 * bv_modulus low ->
  bv_unsigned (bv_and value mask) = bv_unsigned value - bv_modulus low.
Proof.
  intros Hwidth Hmask Hrange.
  rewrite bv_and_unsigned Hmask.
  rewrite <- (bv_wrap_land low (bv_unsigned value)).
  rewrite <- (bv_wrap_sub_modulus_1 low (bv_unsigned value)).
  apply bv_wrap_small. lia.
Qed.

Lemma zesu_guard_mask_signed_value (width low : N) (value : bv low) (mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (Z_to_bv width (bv_signed value)) mask) = bv_unsigned value.
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask.
  rewrite <- (bv_wrap_land low (bv_unsigned (Z_to_bv width (bv_signed value)))).
  rewrite Z_to_bv_unsigned bv_wrap_bv_wrap; last exact Hwidth.
  unfold bv_signed, bv_swrap. rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned value + bv_half_modulus low - bv_half_modulus low)
    with (bv_unsigned value) by ring.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma zesu_guard_signed_negative (width : N) (value : bv width) :
  width <> 0%N ->
  (bv_signed value < 0 <-> bv_half_modulus width <= bv_unsigned value).
Proof.
  intro Hwidth.
  pose proof (bv_unsigned_in_range width value) as Hrange.
  pose proof (bv_half_modulus_nonneg width) as Hhalf.
  pose proof (bv_half_modulus_twice width Hwidth) as Hmodulus.
  unfold bv_signed, bv_swrap.
  destruct (Z_le_gt_dec (bv_half_modulus width) (bv_unsigned value)).
  - rewrite <- (bv_wrap_sub_modulus_1 width
      (bv_unsigned value + bv_half_modulus width)).
    rewrite bv_wrap_small; lia.
  - rewrite bv_wrap_small; lia.
Qed.


Lemma zesu_guard_bv_eq_iff (width : N) (left right : bv width) :
  left = right <-> bv_unsigned left = bv_unsigned right.
Proof. split; [apply f_equal | apply bv_eq]. Qed.

Lemma guard_truncate_one_wrap (width : N) (value : Z) :
  bv_modulus width <= value < 2 * bv_modulus width ->
  bv_unsigned (Z_to_bv width value) = value - bv_modulus width.
Proof.
  intro Hrange. rewrite Z_to_bv_unsigned.
  rewrite <- (bv_wrap_sub_modulus_1 width value).
  apply bv_wrap_small. lia.
Qed.

(* Closed widths select a presentation. The source supplies every value bound. *)
Ltac zesu_bias_unsigned_as_signed wide word :=
  let T := type of word in
  lazymatch T with
  | bv ?width =>
      VmClosed.zesu_vm_closed width;
      VmClosed.zesu_vm_closed wide;
      let modulus := eval vm_compute in (bv_modulus width) in
      let half := eval vm_compute in (bv_half_modulus wide) in
      let Hfits := fresh "HbiasedSignedWidth" in
      assert (Hfits : modulus <= half) by (vm_compute; congruence);
      rewrite bv_zero_extend_signed;
      apply bv_swrap_small;
      let Hrange := fresh "HbiasedUnsignedRange" in
      pose proof (bv_unsigned_in_range width word) as Hrange;
      change (-half <= bv_unsigned word < half);
      change (0 <= bv_unsigned word < modulus) in Hrange;
      clear - Hrange Hfits;
      revert Hrange;
      generalize (bv_unsigned word);
      intros; Lia.lia
  end.

Ltac zesu_bias_byte_base width byte inner :=
  VmClosed.zesu_vm_closed width;
  VmClosed.zesu_vm_closed inner;
  let Hwidth := fresh "HbiasedByteWidth" in
  assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
  let Hinner := fresh "HbiasedInnerMask" in
  assert (Hinner : bv_unsigned inner = Z.ones (Z.of_N 8)) by
    (vm_compute; reflexivity);
  change (bv_unsigned (bv_and (Z_to_bv width (bv_signed byte)) inner) =
    bv_unsigned byte);
  exact (zesu_guard_mask_signed_value width 8 byte inner Hwidth Hinner).

Ltac zesu_bias_one_wrap byte delta modulus :=
  repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end;
  multimatch goal with
  | Hlower : (?lower <= bv_unsigned byte),
    Hupper : (bv_unsigned byte <= ?upper) |- _ =>
      VmClosed.zesu_vm_closed lower;
      VmClosed.zesu_vm_closed upper;
      clear - Hlower Hupper;
      revert Hlower Hupper;
      generalize (bv_unsigned byte);
      intros; Lia.lia
  end.

Ltac zesu_bias_mask_image width byte base inner offset mask masked :=
  VmClosed.zesu_vm_closed width;
  VmClosed.zesu_vm_closed offset;
  VmClosed.zesu_vm_closed mask;
  assert_fails (has_evar byte);
  let delta := eval vm_compute in (bv_unsigned offset) in
  let low := eval vm_compute in (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
  let modulus := eval vm_compute in (bv_modulus low) in
  let Hwidth := fresh "HbiasedMaskWidth" in
  assert (Hwidth : (low <= width)%N) by (vm_compute; congruence);
  let Hmask := fresh "HbiasedLowMask" in
  assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
    (vm_compute; reflexivity);
  let Hbase := fresh "HbiasedByteBase" in
  assert (Hbase : bv_unsigned base = bv_unsigned byte) by
    zesu_bias_byte_base width byte inner;
  let Hoffset := fresh "HbiasedOffset" in
  assert (Hoffset : offset = Z_to_bv width delta) by
    (apply bv_eq; vm_compute; reflexivity);
  let Hshape := fresh "HbiasedMaskShape" in
  assert (Hshape : masked = bv_and (base + Z_to_bv width delta) mask) by
    first [exact (f_equal (fun rhs => bv_and (base + rhs) mask) Hoffset) |
      rewrite bv_add_0_r; reflexivity];
  let Hrange := fresh "HbiasedOneWrap" in
  assert (Hrange : bv_modulus low <= bv_unsigned base + delta <
      2 * bv_modulus low) by
    (rewrite Hbase;
     change (modulus <= bv_unsigned byte + delta < 2 * modulus);
     zesu_bias_one_wrap byte delta modulus);
  rewrite Hshape;
  rewrite (zesu_unsigned_low_mask_add_sub_modulus
      width low base mask delta Hwidth Hmask Hrange);
  rewrite Hbase;
  lazymatch goal with
  | |- _ = ?rhs => change (bv_unsigned byte + delta - modulus = rhs)
  end.

(* The pure leaf fixes the requested result. No branch value is selected. *)
Ltac zesu_source_biased_mask_goal :=
  solve [
    lazymatch goal with
    | |- (bv_unsigned ?byte - ?difference < bv_unsigned ?limit)%Z =>
      assert_fails (has_evar byte);
      assert_fails (has_evar limit);
      VmClosed.zesu_vm_closed difference;
      multimatch goal with
      | Hbranch : ~ (bv_signed (bv_zero_extend ?wide ?masked) >=
          bv_signed (bv_zero_extend ?wide limit))%Z |- _ =>
        let Hview := fresh "HbiasedBranchView" in
        pose proof Hbranch as Hview;
        let Hleft := fresh "HbiasedLeftView" in
        assert (Hleft : bv_signed (bv_zero_extend wide masked) =
            bv_unsigned masked) by zesu_bias_unsigned_as_signed wide masked;
        let Hright := fresh "HbiasedRightView" in
        assert (Hright : bv_signed (bv_zero_extend wide limit) =
            bv_unsigned limit) by zesu_bias_unsigned_as_signed wide limit;
        rewrite Hleft in Hview;
        rewrite Hright in Hview;
        let Himage := fresh "HbiasedImage" in
        lazymatch masked with
        | bv_and (bv_add (bv_and (bv_sign_extend ?width byte) ?inner) ?offset) ?mask =>
            VmClosed.zesu_vm_closed width;
            VmClosed.zesu_vm_closed inner;
            VmClosed.zesu_vm_closed offset;
            VmClosed.zesu_vm_closed mask;
            let delta := eval vm_compute in (bv_unsigned offset) in
            let low := eval vm_compute in (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
            let modulus := eval vm_compute in (bv_modulus low) in
            let expected := eval vm_compute in (modulus - delta) in
            constr_eq difference expected;
            let base := constr:(bv_and (bv_sign_extend width byte) inner) in
            assert (Himage : bv_unsigned masked = bv_unsigned byte - difference) by
              (zesu_bias_mask_image width byte base inner offset mask masked; ring)
        | bv_and (bv_and (bv_sign_extend ?width byte) ?inner) ?mask =>
            VmClosed.zesu_vm_closed width;
            VmClosed.zesu_vm_closed inner;
            VmClosed.zesu_vm_closed mask;
            let low := eval vm_compute in (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
            let modulus := eval vm_compute in (bv_modulus low) in
            constr_eq difference modulus;
            let base := constr:(bv_and (bv_sign_extend width byte) inner) in
            let offset := constr:(Z_to_bv width 0) in
            assert (Himage : bv_unsigned masked = bv_unsigned byte - difference) by
              (zesu_bias_mask_image width byte base inner offset mask masked; ring)
        end;
        rewrite Himage in Hview;
        rewrite Z.ge_le_iff in Hview;
        apply Z.nle_gt in Hview;
        exact Hview
      end
    end].

Ltac zesu_source_biased_mask_fact requested :=
  lazymatch requested with
  | ?left /\ ?right =>
      zesu_source_biased_mask_fact left;
      zesu_source_biased_mask_fact right
  | _ =>
      tryif has_evar requested then idtac else
        tryif (match goal with _ : requested |- _ => idtac end) then idtac else
          let Hview := fresh "HsourceBiasedMask" in
          tryif (assert (Hview : requested) by zesu_source_biased_mask_goal)
          then idtac else idtac
  end.

Ltac zesu_source_biased_mask_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_biased_mask_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_biased_mask_tree left;
      zesu_source_biased_mask_tree right
  | _ => idtac
  end.

(* Proposed addition to BitvectorFacts.v. No machine address or contract occurs. *)
Lemma zesu_single_bit_land_zero (width : N) (index : Z) (word : bv width) :
  (0 <= index < Z.of_N width)%Z ->
  Z.land (bv_unsigned word) (2 ^ index) = 0%Z ->
  bv_extract (Z.to_N index) 1 word = (0%bv : bv 1).
Proof.
 intros [Hnonnegative Hbelow] Hland.
 assert (Hpower : (0 < 2 ^ index)%Z) by (apply Z.pow_pos_nonneg; lia).
 pose proof (f_equal (fun value : Z => Z.shiftr value index) Hland) as Hshift.
 cbv beta iota zeta in Hshift.
 rewrite Z.shiftr_land in Hshift.
 rewrite !Z.shiftr_div_pow2 in Hshift; try lia.
 rewrite Z.div_same in Hshift; try lia.
 apply bv_eq; rewrite bv_extract_unsigned Z2N.id; try lia.
 change ((Z.shiftr (bv_unsigned word) index) mod (2 ^ 1) = 0)%Z.
 rewrite Z.shiftr_div_pow2; try lia.
 rewrite <- Z.land_ones; try lia.
 change (Z.land (bv_unsigned word / 2 ^ index) 1 = 0)%Z.
 exact Hshift.
Qed.

Ltac zesu_source_single_bit_zero_view source word width mask :=
  assert_fails (has_evar word);
  ZesuSsz.Automation.VmClosed.zesu_vm_closed width;
  ZesuSsz.Automation.VmClosed.zesu_vm_closed mask;
  let positive := eval vm_compute in (0 <? mask)%Z in constr_eq positive true;
  let index := eval vm_compute in (Z.log2 mask) in
  let single := eval vm_compute in (Z.eqb mask (2 ^ index)) in constr_eq single true;
  let within := eval vm_compute in (index <? Z.of_N width)%Z in constr_eq within true;
  let bit := eval vm_compute in (Z.to_N index) in
  assert_fails ltac:(idtac; match goal with
    _ : bv_extract bit 1 word = (0%bv : bv 1),
    _ : bv_extract bit 1 word <> (1%bv : bv 1),
    _ : bv_unsigned (bv_extract bit 1 word) = 0%Z,
    _ : bv_unsigned (bv_extract bit 1 word) <> 1%Z |- _ => idtac end);
  tryif match goal with _ : bv_extract bit 1 word = (0%bv : bv 1) |- _ => idtac end
  then idtac else (
  let Hland := fresh "HsingleBitLand" in
  assert (Hland : (Z.land (bv_unsigned word) (2 ^ index) = 0)%Z) by
    (first [
      let Hsource := fresh "HsingleBitSource" in
      pose proof (f_equal (@bv_unsigned width) source) as Hsource;
      change (Z.land (bv_unsigned word) (2 ^ index) = 0)%Z in Hsource;
      exact Hsource
    | exact source]);
  let view := fresh "HsingleBitZero" in
  assert (view : bv_extract bit 1 word = (0%bv : bv 1)) by
    (apply (zesu_single_bit_land_zero width index word);
      [split; ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide | exact Hland]);
  clear Hland);
  tryif match goal with _ : bv_extract bit 1 word <> (1%bv : bv 1) |- _ => idtac end
  then idtac else (
    let zero := match goal with Hzero : bv_extract bit 1 word = (0%bv : bv 1) |- _ => Hzero end in
    let different := fresh "HsingleBitNotOne" in
    assert (different : bv_extract bit 1 word <> (1%bv : bv 1)) by
      (rewrite zero; discriminate));
  let zero := match goal with Hzero : bv_extract bit 1 word = (0%bv : bv 1) |- _ => Hzero end in
  tryif match goal with _ : bv_unsigned (bv_extract bit 1 word) = 0%Z |- _ => idtac end
  then idtac else (let unsignedZero := fresh "HsingleBitUnsignedZero" in
    assert (unsignedZero : bv_unsigned (bv_extract bit 1 word) = 0%Z) by (rewrite zero; reflexivity));
  tryif match goal with _ : bv_unsigned (bv_extract bit 1 word) <> 1%Z |- _ => idtac end
  then idtac else (let unsignedNotOne := fresh "HsingleBitUnsignedNotOne" in
    assert (unsignedNotOne : bv_unsigned (bv_extract bit 1 word) <> 1%Z) by (rewrite zero; discriminate)).

Ltac zesu_source_single_bit_zero_views :=
  repeat multimatch goal with
  | source : @bv_and ?width ?word ?mask = ?zero |- _ =>
      constr_eq zero constr:((0%bv : bv width));
      ZesuSsz.Automation.VmClosed.zesu_vm_closed mask;
      let magnitude := eval vm_compute in (bv_unsigned mask) in
      zesu_source_single_bit_zero_view source word width magnitude
  | source : Z.land (bv_unsigned ?word) ?mask = 0%Z |- _ =>
      let width := lazymatch type of word with bv ?width => width end in
      zesu_source_single_bit_zero_view source word width mask
  end.

Ltac zesu_source_unsigned_bound :=
  lazymatch goal with
  | |- bv_unsigned ?word <= ?bound =>
    assert_fails (has_evar word);
    let kind := type of word in lazymatch kind with bv ?width =>
      ZesuSsz.Automation.VmClosed.zesu_vm_closed width;
      ZesuSsz.Automation.VmClosed.zesu_vm_closed bound;
      let limit := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_modulus width) in
      let ceiling := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed bound in
      let adequate := fresh "HunsignedCeiling" in
      assert (adequate : (limit - 1 <= ceiling)%Z) by
        ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide;
      let range := fresh "HunsignedRange" in
      pose proof (bv_unsigned_in_range width word) as range;
      change (0 <= bv_unsigned word < limit)%Z in range;
      change (bv_unsigned word <= ceiling)%Z;
      clear -range adequate; Lia.lia
    end
  | |- bv_unsigned ?word < ?bound =>
    assert_fails (has_evar word);
    let kind := type of word in lazymatch kind with bv ?width =>
      ZesuSsz.Automation.VmClosed.zesu_vm_closed width;
      ZesuSsz.Automation.VmClosed.zesu_vm_closed bound;
      let limit := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_modulus width) in
      let ceiling := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed bound in
      let adequate := fresh "HunsignedCeiling" in
      assert (adequate : (limit <= ceiling)%Z) by
        ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide;
      let range := fresh "HunsignedRange" in
      pose proof (bv_unsigned_in_range width word) as range;
      change (0 <= bv_unsigned word < limit)%Z in range;
      change (bv_unsigned word < ceiling)%Z;
      clear -range adequate; Lia.lia
    end
  end.
