Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.CodecArrayRead.
From Coq Require Import Lia.
From stdpp Require Import list.
Require Import ZesuSsz.Automation.All.
#[local] Instance codec_control_enabled : ZesuStepCodecArrayRead := {}.

Lemma codec_direct_integer (value : Z) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat 1) (0%bv :: bv_to_little_endian 8 8 value)))) =
  Z_to_bv 64 value.
Proof. zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_direct_word (value : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat 1) (0%bv :: bv_to_little_endian 8 8 (bv_unsigned value))))) = value.
Proof. zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_literal_extent : (Z.to_nat 0 + N.to_nat 8 <= 16)%nat.
Proof. zesu_codec_array_read_sidecond. Qed.

Lemma codec_refuses_short_slice (value : Z) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 7 (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 8 value)))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 7 (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 8 value)))).
Proof. Fail zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_refuses_symbolic_count (count : nat) (value : Z) :
  Z_to_bv 64 (little_endian_to_bv 8 (take count (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 8 value)))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take count (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 8 value)))).
Proof. Fail zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_refuses_symbolic_offset (offset value : Z) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset)
    (0%bv :: bv_to_little_endian 8 8 value)))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset)
    (0%bv :: bv_to_little_endian 8 8 value)))).
Proof. Fail zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_refuses_other_modulus (value : Z) :
  Z_to_bv 64 (little_endian_to_bv 16 (take 8 (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 16 value)))) =
  Z_to_bv 64 (little_endian_to_bv 16 (take 8 (drop (Z.to_nat 1)
    (0%bv :: bv_to_little_endian 8 16 value)))).
Proof. Fail zesu_codec_array_direct_value. reflexivity. Qed.

Lemma codec_refuses_unrelated : True.
Proof. Fail zesu_codec_array_direct_value. exact I. Qed.
