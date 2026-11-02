Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodecArrayRange.
From Coq Require Import Lists.List ZArith.ZArith.
Local Open Scope Z_scope.

Definition codec_control_extent : Z := 16.

Lemma codec_range_symbolic_payload (base payload : Z) :
  base - codec_control_extent <= base - 8 <
  base - codec_control_extent + 8 +
    Z.of_nat (length (bv_to_little_endian 8 8 payload)).
Proof.
  Fail zesu_codec_array_range.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  zesu_codec_array_range.
Qed.
Print Assumptions codec_range_symbolic_payload.

Goal forall (count base payload : Z), 1 <= count ->
  base <= base < base + Z.of_nat (length (bv_to_little_endian count 8 payload)).
Proof.
  intros count base payload Hcount.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.

Goal forall (width : N) (base payload : Z),
  base <= base < base + Z.of_nat (length (bv_to_little_endian 8 width payload)).
Proof.
  intros width base payload.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.

Goal forall (extent base payload : Z),
  base - extent <= base - 8 <
  base - extent + Z.of_nat (length (bv_to_little_endian 8 8 payload)).
Proof.
  intros extent base payload.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.

Goal forall (base payload : Z),
  base <= base < base + Z.of_nat (length (bv_to_little_endian (-1) 8 payload)).
Proof.
  intros base payload.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.

Goal forall (base payload : Z),
  base <= base < base + Z.of_nat (length (bv_to_little_endian 0 8 payload)).
Proof.
  intros base payload.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.

Lemma codec_range_wrong_shape (base : Z) : base = base.
Proof.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
  reflexivity.
Qed.
Print Assumptions codec_range_wrong_shape.

(* A nonempty array also refuses a pointer exactly at its upper boundary. *)
Goal forall (base payload : Z),
  base - 16 <= base - 8 <
  base - 16 + Z.of_nat (length (bv_to_little_endian 8 8 payload)).
Proof.
  intros base payload.
  assert (enabled : ZesuStepCodecArrayRange) by constructor.
  Fail zesu_codec_array_range.
Abort.
