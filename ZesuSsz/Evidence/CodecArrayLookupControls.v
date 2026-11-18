(* Unverified source controls. No test in this file has executed. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.CodecArrayLookup.
From stdpp Require Import bitvector.definitions list.
From Coq Require Import Lists.List ZArith.ZArith.
Local Open Scope Z_scope.

Lemma owned_codec_length_control (count : Z) (width : N) (value : Z)
    (Hcount : 0 <= count) :
  length (bv_to_little_endian count width value) = Z.to_nat count.
Proof.
  zesu_owned_codec_length_facts (bv_to_little_endian count width value).
  assumption.
Qed.

Lemma owned_codec_length_idempotent (count : Z) (width : N) (value : Z)
    (Hcount : 0 <= count) :
  length (bv_to_little_endian count width value) = Z.to_nat count.
Proof.
  zesu_owned_codec_length_facts (bv_to_little_endian count width value).
  Fail progress zesu_owned_codec_length_facts (bv_to_little_endian count width value).
  assumption.
Qed.

Lemma owned_codec_length_missing_bound (count : Z) (width : N) (value : Z) :
  length (bv_to_little_endian count width value) = Z.to_nat count.
Proof.
  Fail progress zesu_owned_codec_length_facts (bv_to_little_endian count width value).
Abort.

Lemma codec_lookup_wrong_shape : True.
Proof.
  assert (enabled : ZesuStepCodecArrayLookup) by constructor.
  Fail zesu_codec_array_lookup.
  exact I.
Qed.

Section memory_controls.
Context `{!islaG Sigma} `{!threadG}.

Lemma codec_lookup_disabled (base : Z) (value : Z) :
  base ↦ₘ∗ (bv_to_little_endian 2 8 value) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 1)))
    (fun _ => True)%I.
Proof.
  iIntros "Hbytes".
  Fail zesu_codec_array_lookup.
Abort.

Lemma codec_lookup_contained (base : Z) (value : Z)
    (Hbase : 0 <= base < bv_modulus 64 - 1) :
  base ↦ₘ∗ (bv_to_little_endian 2 8 value) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 1)))
    (fun _ => True)%I.
Proof.
  assert (enabled : ZesuStepCodecArrayLookup) by constructor.
  iIntros "Hbytes".
  zesu_codec_array_lookup; repeat liStep; done.
Qed.

Lemma codec_lookup_missing_range (base : Z) (value : Z) :
  base ↦ₘ∗ (bv_to_little_endian 2 8 value) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 1)))
    (fun _ => True)%I.
Proof.
  assert (enabled : ZesuStepCodecArrayLookup) by constructor.
  iIntros "Hbytes".
  Fail zesu_codec_array_lookup.
Abort.

Lemma codec_lookup_symbolic_offset (base : Z) (offset : bv 64) (value : Z) :
  base ↦ₘ∗ (bv_to_little_endian 2 8 value) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + offset)))
    (fun _ => True)%I.
Proof.
  assert (enabled : ZesuStepCodecArrayLookup) by constructor.
  iIntros "Hbytes".
  Fail zesu_codec_array_lookup.
Abort.
End memory_controls.
