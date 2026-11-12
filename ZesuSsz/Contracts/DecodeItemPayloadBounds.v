From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.

Import ListNotations.
Open Scope Z_scope.

(* The 64-bit words that a caller's loads read at byte offsets 0 and 8 of a
   byte list, in the form the block generator renders such a load. *)
Notation listWord64At0 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 7%nat bytes (BV 8%N 0%Z)) (List.nth 6%nat bytes (BV 8%N 0%Z)))
    (List.nth 5%nat bytes (BV 8%N 0%Z))) (List.nth 4%nat bytes (BV 8%N 0%Z)))
    (List.nth 3%nat bytes (BV 8%N 0%Z))) (List.nth 2%nat bytes (BV 8%N 0%Z)))
    (List.nth 1%nat bytes (BV 8%N 0%Z))) (List.nth 0%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation listWord64At8 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 15%nat bytes (BV 8%N 0%Z)) (List.nth 14%nat bytes (BV 8%N 0%Z)))
    (List.nth 13%nat bytes (BV 8%N 0%Z))) (List.nth 12%nat bytes (BV 8%N 0%Z)))
    (List.nth 11%nat bytes (BV 8%N 0%Z))) (List.nth 10%nat bytes (BV 8%N 0%Z)))
    (List.nth 9%nat bytes (BV 8%N 0%Z))) (List.nth 8%nat bytes (BV 8%N 0%Z))) (only parsing).

Lemma concatByteUnsigned n n1 (x : bv n1) (b : bv 8) :
  n = (n1 + 8)%N -> bv_unsigned (bv_concat n x b) = bv_unsigned x * 256 + bv_unsigned b.
Proof.
  intros ->. rewrite bv_concat_unsigned by done.
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ Z.of_N 8) with 256.
  rewrite <- Z.add_nocarry_lor; [lia|].
  rewrite <- (Z.mod_small (bv_unsigned b) 256) by lia.
  change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm (bv_unsigned b) (Z.ones 8)), Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_mul by lia. apply Z.land_0_l.
Qed.

Lemma listWord64At0Value (bytes : list byte) value :
  word64At bytes 0 value -> bv_unsigned (listWord64At0 bytes) = value.
Proof.
  unfold word64At. intros [Hlen <-].
  do 8 (destruct bytes as [|? bytes]; [simpl in Hlen; discriminate|]).
  cbn [List.nth skipn firstn littleEndian].
  rewrite ?firstn_O; cbn [littleEndian].
  rewrite !concatByteUnsigned by reflexivity.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

Lemma listWord64At8Value (bytes : list byte) value :
  word64At bytes 8 value -> bv_unsigned (listWord64At8 bytes) = value.
Proof.
  unfold word64At. intros [Hlen <-].
  do 16 (destruct bytes as [|? bytes]; [simpl in Hlen; discriminate|]).
  cbn [List.nth skipn firstn littleEndian]. rewrite ?firstn_O; cbn [littleEndian].
  rewrite !concatByteUnsigned by reflexivity.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

Lemma errorResult40Word8 (after : list byte) :
  errorResult40 after -> bv_unsigned (listWord64At8 after) = 0.
Proof.
  unfold errorResult40. intros [Hlen Hbytes].
  do 16 (destruct after as [|? after]; [simpl in Hlen; discriminate|]).
  cbn [List.nth]. rewrite !concatByteUnsigned by reflexivity.
  pose proof (Hbytes 8%nat ltac:(lia)) as H8. pose proof (Hbytes 9%nat ltac:(lia)) as H9.
  pose proof (Hbytes 10%nat ltac:(lia)) as H10. pose proof (Hbytes 11%nat ltac:(lia)) as H11.
  pose proof (Hbytes 12%nat ltac:(lia)) as H12. pose proof (Hbytes 13%nat ltac:(lia)) as H13.
  pose proof (Hbytes 14%nat ltac:(lia)) as H14. pose proof (Hbytes 15%nat ltac:(lia)) as H15.
  unfold byteAt in *. cbn in H8, H9, H10, H11, H12, H13, H14, H15. simplify_eq.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

(* A success header is at most 9 bytes, and checkedPayload fits header and
   payload in the input modulo 2^64. The empty string 0x80 has no payload. *)
Lemma candidateDecodeItemSuccessBounds input isList headerLength payloadLength :
  candidateDecodeItem input = candidateSuccess isList headerLength payloadLength ->
  0 <= headerLength <= 9 /\
  (headerLength + payloadLength) mod word64Modulus <= Z.of_nat (length input) /\
  (forall prefix rest, input = prefix :: rest -> bv_unsigned prefix = 128 -> payloadLength = 0).
Proof.
  destruct input as [|prefix rest]; [discriminate|].
  pose proof (bv_unsigned_in_range _ prefix) as Hp. unfold bv_modulus in Hp.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 256 in Hp.
  unfold candidateDecodeItem, checkedPayload. cbn zeta. cbn [length]. intros H.
  change (2 ^ 64) with 18446744073709551616 in *.
  repeat (case_match; simplify_eq);
    rewrite ?andb_true_iff, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *.
  all: change (MachineWord.MachineWord.Z_idx 8) with 8%N in *.
  all: split; [lia|split].
  all: try (intros ? ? [= <- <-] ?; lia).
  all: first [rewrite Z.mod_small by lia; lia | lia].
Qed.

(* decodeItem's C1-B meaning places a nonempty payload of fewer than 2^64 - 9
   bytes inside the input array. The bound excludes the wrap case. *)
Lemma decodeItemPayloadInInput inputPointer input before after :
  C1BResult inputPointer input before after ->
  0 < bv_unsigned (listWord64At8 after) ->
  bv_unsigned (listWord64At8 after) < 18446744073709551607 ->
  inputPointer <= bv_unsigned (listWord64At0 after) /\
  bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    inputPointer + Z.of_nat (length input).
Proof.
  unfold C1BResult, candidateResult40. intros (_ & Hresult & _) Hpos Hsmall.
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - rewrite (errorResult40Word8 after Hresult) in Hpos. lia.
  - destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hfit & H128).
    destruct Hresult as (_ & _ & H0 & H8 & _).
    apply listWord64At8Value in H8. rewrite H8 in *.
    apply listWord64At0Value in H0. rewrite H0.
    destruct input as [|prefix rest]; [discriminate|].
    destruct (Z.eqb_spec (bv_unsigned prefix) 128) as [E|E].
    + rewrite (H128 prefix rest eq_refl E) in Hpos. lia.
    + change (2 ^ 64) with 18446744073709551616 in Hfit.
      rewrite Z.mod_small in Hfit by lia. lia.
Qed.

(* The call post states C1BResult on the caller's argument 1, so the callee
   output bounds the payload by that pointer and the input length. *)
#[export] Instance decodeItemCallPayloadInInputDerivedFacts
    argv0 argv1 rest sp inputEnd input before after :
  ZesuDerivedFacts
    (DecodeMeaningModuloKnownBugs
       (decodeItemCallDataArgs (argv0 :: argv1 :: rest) sp inputEnd input before) after)
    (0 < bv_unsigned (listWord64At8 after) ->
     bv_unsigned (listWord64At8 after) < 18446744073709551607 ->
     bv_unsigned argv1 <= bv_unsigned (listWord64At0 after) /\
     bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
       bv_unsigned argv1 + Z.of_nat (length input)).
Proof. intros [Hc1b _]. exact (decodeItemPayloadInInput _ _ _ _ Hc1b). Qed.
