From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.

Import ListNotations.
Open Scope Z_scope.

(* Proofs of decodeItem's interface lemmas, over the real definitions.
   ZesuSsz/Interfaces/DecodeItem.v (generated from
   ZesuSsz/Contracts/proved_functions.json) states each lemma over the
   sealed domain and meaning and checks it once against the lemma here,
   inside the sealed implementation. Callers never import this module. *)

(* The 64-bit word at byte offset 24 of a byte list, in the load form the
   block generator renders (listWord64At0 and listWord64At8 are beside it). *)
Notation listWord64At24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).

Lemma byteAtNth (bytes : list byte) index value :
  byteAt bytes index value -> bv_unsigned (List.nth index bytes (BV 8%N 0%Z)) = value.
Proof.
  unfold byteAt. destruct (nth_error bytes index) as [b|] eqn:E; [|discriminate].
  intros [= <-]. by rewrite (nth_error_nth _ _ _ E).
Qed.

Lemma listWord64At24Value (bytes : list byte) value :
  word64At bytes 24 value -> bv_unsigned (listWord64At24 bytes) = value.
Proof.
  unfold word64At. intros [Hlen <-].
  do 32 (destruct bytes as [|? bytes]; [simpl in Hlen; discriminate|]).
  cbn [List.nth skipn firstn littleEndian]. rewrite ?firstn_O; cbn [littleEndian].
  rewrite !concatByteUnsigned by reflexivity.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

Lemma errorResult40Word0 (after : list byte) :
  errorResult40 after -> bv_unsigned (listWord64At0 after) = 0.
Proof.
  unfold errorResult40. intros [Hlen Hbytes].
  do 8 (destruct after as [|? after]; [simpl in Hlen; discriminate|]).
  cbn [List.nth]. rewrite !concatByteUnsigned by reflexivity.
  pose proof (Hbytes 0%nat ltac:(lia)) as H0. pose proof (Hbytes 1%nat ltac:(lia)) as H1.
  pose proof (Hbytes 2%nat ltac:(lia)) as H2. pose proof (Hbytes 3%nat ltac:(lia)) as H3.
  pose proof (Hbytes 4%nat ltac:(lia)) as H4. pose proof (Hbytes 5%nat ltac:(lia)) as H5.
  pose proof (Hbytes 6%nat ltac:(lia)) as H6. pose proof (Hbytes 7%nat ltac:(lia)) as H7.
  unfold byteAt in *. cbn in H0, H1, H2, H3, H4, H5, H6, H7. simplify_eq.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

(* C1BResult in the caller's terms: the output is 40 bytes; byte 32 is the
   error tag (4 on error, 0 on success); an error clears the payload words;
   a success has an isList byte of 0 or 1 and a consumed count that fits in
   the input (checkedPayload). *)
Lemma C1BResultCallerFacts inputPointer input before after :
  C1BResult inputPointer input before after ->
  (List.length after = 40)%nat /\
  inputAddressFits inputPointer input /\
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 0 \/
   bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 4) /\
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 4 ->
   bv_unsigned (listWord64At0 after) = 0 /\ bv_unsigned (listWord64At8 after) = 0) /\
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 0 ->
   bv_unsigned (List.nth 16 after (BV 8%N 0%Z)) <= 1 /\
   bv_unsigned (listWord64At24 after) <= Z.of_nat (length input)).
Proof.
  unfold C1BResult, candidateResult40. intros (Hfits & Hresult & _).
  split; [|split; [exact Hfits|]].
  - destruct (candidateDecodeItem input); [exact (proj1 Hresult)|exact (proj1 (proj2 Hresult))].
  - destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
    + pose proof (byteAtNth _ _ _ (proj2 Hresult 32%nat ltac:(lia))) as Htag.
      cbn in Htag. rewrite Htag.
      split; [by right|]. split; [|lia].
      intros _. split; [exact (errorResult40Word0 _ Hresult)|exact (errorResult40Word8 _ Hresult)].
    + destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (_ & Hfit & _).
      destruct Hresult as (_ & _ & _ & _ & Hlist & Hconsumed & H32 & _).
      apply byteAtNth in H32. apply byteAtNth in Hlist. apply listWord64At24Value in Hconsumed.
      rewrite H32. split; [by left|]. split; [lia|].
      intros _. rewrite Hlist, Hconsumed. split; [destruct isList; lia|exact Hfit].
Qed.

Lemma decodeItemMeaningC1B args after :
  DecodeMeaningModuloKnownBugs args after ->
  C1BResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after.
Proof. by intros [Hc1b _]. Qed.

Lemma errorResult40Word24 (after : list byte) :
  errorResult40 after -> bv_unsigned (listWord64At24 after) = 0.
Proof.
  unfold errorResult40. intros [Hlen Hbytes].
  do 32 (destruct after as [|? after]; [simpl in Hlen; discriminate|]).
  cbn [List.nth]. rewrite !concatByteUnsigned by reflexivity.
  pose proof (Hbytes 24%nat ltac:(lia)) as H24. pose proof (Hbytes 25%nat ltac:(lia)) as H25.
  pose proof (Hbytes 26%nat ltac:(lia)) as H26. pose proof (Hbytes 27%nat ltac:(lia)) as H27.
  pose proof (Hbytes 28%nat ltac:(lia)) as H28. pose proof (Hbytes 29%nat ltac:(lia)) as H29.
  pose proof (Hbytes 30%nat ltac:(lia)) as H30. pose proof (Hbytes 31%nat ltac:(lia)) as H31.
  unfold byteAt in *. cbn in H24, H25, H26, H27, H28, H29, H30, H31. simplify_eq.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

(* A success consumes at most the input; an error writes 0. *)
Lemma decodeItemConsumedInInput inputPointer input before after :
  C1BResult inputPointer input before after ->
  bv_unsigned (listWord64At24 after) <= Z.of_nat (length input).
Proof.
  unfold C1BResult, candidateResult40. intros (_ & Hresult & _).
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - rewrite (errorResult40Word24 after Hresult). lia.
  - destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (_ & Hfit & _).
    destruct Hresult as (_ & _ & _ & _ & _ & H24 & _).
    rewrite (listWord64At24Value _ _ H24). exact Hfit.
Qed.

(* ---- The interface lemmas (proof sources of proved_functions.json). ---- *)

Lemma decodeItemMeaningLength args after :
  DecodeMeaningModuloKnownBugs args after -> (List.length after = 40)%nat.
Proof. intros H. exact (proj1 (C1BResultCallerFacts _ _ _ _ (decodeItemMeaningC1B _ _ H))). Qed.

(* A nonempty payload shorter than 2^64 - 9 lies inside the input array at
   the caller's argument 1. *)
Lemma decodeItemMeaningPayloadInInput argv0 argv1 rest sp inputEnd input before after :
  DecodeMeaningModuloKnownBugs
    (decodeItemCallDataArgs (argv0 :: argv1 :: rest) sp inputEnd input before) after ->
  0 < bv_unsigned (listWord64At8 after) ->
  bv_unsigned (listWord64At8 after) < 18446744073709551607 ->
  bv_unsigned argv1 <= bv_unsigned (listWord64At0 after) /\
  bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned argv1 + Z.of_nat (length input).
Proof. intros H. exact (decodeItemPayloadInInput _ _ _ _ (decodeItemMeaningC1B _ _ H)). Qed.

Lemma decodeItemMeaningInputFits argv0 argv1 rest sp inputEnd input before after :
  DecodeMeaningModuloKnownBugs
    (decodeItemCallDataArgs (argv0 :: argv1 :: rest) sp inputEnd input before) after ->
  0 <= bv_unsigned argv1 /\
  bv_unsigned argv1 + Z.of_nat (length input) < 18446744073709551616.
Proof.
  intros H. exact (proj1 (proj2 (C1BResultCallerFacts _ _ _ _ (decodeItemMeaningC1B _ _ H)))).
Qed.

Lemma decodeItemMeaningKind args after :
  DecodeMeaningModuloKnownBugs args after ->
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 0 \/
   bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 4) /\
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 4 ->
   bv_unsigned (listWord64At0 after) = 0 /\ bv_unsigned (listWord64At8 after) = 0) /\
  (bv_unsigned (List.nth 32 after (BV 8%N 0%Z)) = 0 ->
   bv_unsigned (List.nth 16 after (BV 8%N 0%Z)) <= 1 /\
   bv_unsigned (listWord64At24 after) <= Z.of_nat (length (decodeItemInputBytes args))).
Proof.
  intros H. exact (proj2 (proj2 (C1BResultCallerFacts _ _ _ _ (decodeItemMeaningC1B _ _ H)))).
Qed.

(* The payload bound in the 8-byte little-endian window form, the form in
   which a caller passes the payload pointer on as a call argument. *)
Lemma decodeItemMeaningPayloadInInputLe argv0 argv1 rest sp inputEnd input before after :
  DecodeMeaningModuloKnownBugs
    (decodeItemCallDataArgs (argv0 :: argv1 :: rest) sp inputEnd input before) after ->
  0 < bv_unsigned (listWord64At8 after) ->
  bv_unsigned (listWord64At8 after) < 18446744073709551607 ->
  bv_unsigned argv1 <= bv_unsigned (leWord64 after 0) /\
  bv_unsigned (leWord64 after 0) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned argv1 + Z.of_nat (length input).
Proof.
  intros H. pose proof (decodeItemMeaningC1B _ _ H) as Hc1b.
  rewrite (decodeItemPayloadPointerLe _ _ _ _ Hc1b).
  exact (decodeItemPayloadInInput _ _ _ _ Hc1b).
Qed.

(* The consumed count (bytes 24..31) never exceeds the input, on success and
   on error: a caller advances its cursor by it. *)
Lemma decodeItemMeaningConsumed argv sp inputEnd input before after :
  DecodeMeaningModuloKnownBugs (decodeItemCallDataArgs argv sp inputEnd input before) after ->
  bv_unsigned (listWord64At24 after) <= Z.of_nat (length input).
Proof. intros H. exact (decodeItemConsumedInInput _ _ _ _ (decodeItemMeaningC1B _ _ H)). Qed.

(* A call-site domain: the length argument is the input's length and the
   input range does not wrap. *)
Lemma decodeItemDomainInput argv0 argv1 argv2 rest sp inputEnd input before :
  decodeItemC1BDomain
    (decodeItemCallDataArgs (argv0 :: argv1 :: argv2 :: rest) sp inputEnd input before) ->
  bv_unsigned argv2 = Z.of_nat (length input) /\
  bv_unsigned argv1 + bv_unsigned argv2 < bv_modulus 64.
Proof.
  intros [Hlen [_ Hlayout]]. unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as (_ & _ & Hfit & _). split; [exact Hlen | exact Hfit].
Qed.

(* A call-site domain: the output buffer the caller passes holds 40 bytes, the
   length a caller's uninitialized frame region must give it. *)
Lemma decodeItemDomainOutput argv sp inputEnd input before :
  decodeItemC1BDomain (decodeItemCallDataArgs argv sp inputEnd input before) ->
  length before = 40%nat.
Proof. intros [_ [Hbefore _]]. exact Hbefore. Qed.

(* The call site establishes the sealed domain from decodeItem's stated
   precondition; a caller's exit composition reads the meaning back. Inside
   the sealed implementation both are the identity. *)
Lemma decodeItemDomainIntro args : decodeItemC1BDomain args -> decodeItemC1BDomain args.
Proof. exact id. Qed.

Lemma decodeItemMeaningLink args after :
  DecodeMeaningModuloKnownBugs args after -> DecodeMeaningModuloKnownBugs args after.
Proof. exact id. Qed.
