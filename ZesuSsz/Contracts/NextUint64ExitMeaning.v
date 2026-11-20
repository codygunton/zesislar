(* The meaning conjunct of nextUint64's return join (block 0x0070), in the
   form the two exit blocks reach it:

     ∃ result : NextUint64Return,
       nextResultBytes result = <stored result bytes> /\
       <stored slice image> = nextUint64SliceImage (nextRestPointer result)
                                                   (nextRestLength result) /\
       nextUint64RootResult (nextUint64Base args) result

   Block 0x0064 (error exit) reaches it with the decodeItem call record and
   the disjunction of the three rejecting branches; block 0x00b8 (success
   exit) with the call record, the accepting guards and the fold of the
   payload into x11. The lemmas here take those facts in the spelling of the
   generated entries (bv_concat chains of List.nth over the decodeItem
   output, the decodeItemCallDataArgs record) and bridge them to the premises
   of ZesuSsz.Compliance.NextUint64Meaning.

   These are pure lemmas: this module is the nextUint64 entry of
   `exit_meaning_modules` in ZesuSsz/Contracts/proved_functions.json, the one
   place where nextUint64 may use decodeItemCallMeaningLink. It holds no
   tactic and no hint; ZesuSsz.Contracts.NextUint64MeaningFacts applies and
   registers the lemmas. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Compliance.NextUint64Meaning.
Import ListNotations.
Open Scope Z_scope.


(* The words nextUint64's branches read from the decodeItem output, as the
   generated entries spell them. *)
Notation nextUint64Status16Word after :=
  (bv_concat 16%N (List.nth 33%nat after (BV 8%N 0%Z)) (List.nth 32%nat after (BV 8%N 0%Z)))
  (only parsing).
Notation nextUint64ListBitWord after :=
  (bv_and (bv_zero_extend 64%N (List.nth 16%nat after (BV 8%N 0%Z))) (BV 64%N 1%Z))
  (only parsing).
Notation nextUint64ConsumedWord bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).

(* ---- word views of the decodeItem output ---- *)
Lemma nextUint64StatusWordValue (after : list byte) :
  length after = 40%nat ->
  bv_unsigned (nextUint64Status16Word after) = nextUint64DecodedStatus after.
Proof.
  intros Hlen. unfold nextUint64DecodedStatus.
  do 34 (destruct after as [|? after]; [simpl in Hlen; discriminate|]).
  cbn [List.nth skipn firstn littleEndian]. rewrite ?firstn_O; cbn [littleEndian].
  rewrite concatByteUnsigned by reflexivity.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

Lemma nextUint64ListBitWordValue (b : byte) :
  bv_unsigned (bv_and (bv_zero_extend 64 b) (BV 64 1)) = Z.land (bv_unsigned b) 1.
Proof.
  rewrite bv_and_unsigned, (bv_zero_extend_unsigned 64 b) by done.
  change (bv_unsigned (BV 64 1)) with 1. reflexivity.
Qed.

Lemma nextUint64PointerWordValue (after : list byte) :
  length after = 40%nat ->
  bv_unsigned (listWord64At0 after) = nextUint64DecodedPointer after.
Proof.
  intros Hlen. apply listWord64At0Value. split; [|reflexivity].
  do 8 (destruct after as [|? after]; [simpl in Hlen; discriminate|]). reflexivity.
Qed.

Lemma nextUint64LengthWordValue (after : list byte) :
  length after = 40%nat ->
  bv_unsigned (listWord64At8 after) = nextUint64DecodedLength after.
Proof.
  intros Hlen. apply listWord64At8Value. split; [|reflexivity].
  do 16 (destruct after as [|? after]; [simpl in Hlen; discriminate|]). reflexivity.
Qed.

Lemma nextUint64ConsumedWordValue (after : list byte) :
  length after = 40%nat ->
  bv_unsigned (nextUint64ConsumedWord after) = nextUint64DecodedConsumed after.
Proof.
  intros Hlen. unfold nextUint64DecodedConsumed.
  do 32 (destruct after as [|? after]; [simpl in Hlen; discriminate|]).
  cbn [List.nth skipn firstn littleEndian]. rewrite ?firstn_O; cbn [littleEndian].
  rewrite !concatByteUnsigned by reflexivity.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *. lia.
Qed.

(* The word that decodeItem's argument registers carry, as the block's
   context spells it after the call: the eight bytes of the value. *)
Lemma nextUint64WordOfBytes (value : Z) :
  0 <= value < 2 ^ 64 -> bv_unsigned (listWord64At0 (word64Bytes value)) = value.
Proof.
  intros Hvalue. apply listWord64At0Value.
  rewrite <- nextUint64Word64BytesEncoding. unfold word64At. cbn [skipn].
  rewrite firstn_all2 by (rewrite length_bv_to_little_endian by lia; cbn; lia).
  split; [rewrite length_bv_to_little_endian by lia; reflexivity|].
  apply (littleEndian_machine_bytes 8). exact Hvalue.
Qed.

Lemma nextUint64CallInputPointer argv sp inputEnd input before :
  decodeItemInputPointer (decodeItemCallDataArgs argv sp inputEnd input before) =
    bv_unsigned (argv !!! 1%nat).
Proof. reflexivity. Qed.

(* ---- block 0x0064: the error exit ---- *)
Lemma nextUint64MeaningError (args : NextUint64Args) (argv : list (bv 64)) (sp : bv 64)
    (inputEnd : Z) (before after bytes image : list byte) :
  nextUint64BoundaryDomain args ->
  length after = 40%nat ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs argv sp inputEnd (nextInputBytes (nextUint64Base args)) before) after ->
  bv_unsigned (argv !!! 1%nat) = nextInputPointer (nextUint64Base args) ->
  (bv_unsigned (nextUint64Status16Word after) <> 0 \/
   (bv_unsigned (nextUint64Status16Word after) = 0 /\
    bv_unsigned (nextUint64ListBitWord after) <> 0) \/
   (bv_unsigned (nextUint64Status16Word after) = 0 /\
    bv_unsigned (nextUint64ListBitWord after) = 0 /\
    8 < bv_unsigned (listWord64At8 after))) ->
  bytes = bv_to_little_endian 8 8 0 ++ bv_to_little_endian 8 8 3 ->
  image = nextUint64SliceImage (nextInputPointer (nextUint64Base args))
    (Z.of_nat (length (nextInputBytes (nextUint64Base args)))) ->
  exists result : NextUint64Return,
    nextResultBytes result = bytes /\
    image = nextUint64SliceImage (nextRestPointer result) (nextRestLength result) /\
    nextUint64RootResult (nextUint64Base args) result.
Proof.
  intros Hdomain Hlen Hcall Hptr Hbranch -> ->.
  exists {| nextResultBytes := nextUint64ErrorBytes;
            nextRestPointer := nextInputPointer (nextUint64Base args);
            nextRestLength := Z.of_nat (length (nextInputBytes (nextUint64Base args))) |}.
  split; [|split; [reflexivity|]].
  - cbn [nextResultBytes]. unfold nextUint64ErrorBytes.
    rewrite !nextUint64Word64BytesEncoding. reflexivity.
  - apply (nextUint64ErrorExitMeaning args
      (decodeItemCallDataArgs argv sp inputEnd (nextInputBytes (nextUint64Base args)) before)
      after Hdomain eq_refl
      ltac:(rewrite nextUint64CallInputPointer; exact Hptr)
      (decodeItemCallMeaningLink _ _ Hcall)).
    rewrite <- nextUint64StatusWordValue, <- nextUint64LengthWordValue by exact Hlen.
    rewrite <- nextUint64ListBitWordValue. tauto.
Qed.

(* The eight little-endian bytes of a value, as the stores of the exit
   blocks spell them (bv_to_little_endian 8 8 unfolded). *)
Notation nextUint64Le8 v :=
  [Z_to_bv 8 (Z.land v (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr v 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr v 8) 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr v 8) 8) 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr v 8) 8) 8) 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr v 8) 8) 8) 8) 8)
     (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr v 8) 8) 8) 8)
     8) 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr v 8)
     8) 8) 8) 8) 8) 8) (Z.ones 8))] (only parsing).

Lemma nextUint64Le8Bytes (v : Z) : nextUint64Le8 v = word64Bytes v.
Proof. rewrite <- nextUint64Word64BytesEncoding. reflexivity. Qed.

Lemma nextUint64InputPointerRange (args : NextUint64Args) :
  nextUint64BoundaryDomain args -> 0 <= nextInputPointer (nextUint64Base args) < 2 ^ 64.
Proof.
  intros Hdomain. destruct (nextUint64DomainFits args Hdomain) as [H0 H1].
  unfold word64Modulus in H1. Zify.zify; xlia Lia.zchecker.
Qed.

Lemma nextUint64InputLengthRange (args : NextUint64Args) :
  nextUint64BoundaryDomain args ->
  0 <= Z.of_nat (length (nextInputBytes (nextUint64Base args))) < 2 ^ 64.
Proof.
  intros Hdomain. destruct (nextUint64DomainFits args Hdomain) as [H0 H1].
  unfold word64Modulus in H1. Zify.zify; xlia Lia.zchecker.
Qed.

(* ---- block 0x00b8: the success exit ---- *)
Lemma nextUint64MeaningSuccess (args : NextUint64Args) (argv : list (bv 64)) (sp : bv 64)
    (inputEnd : Z) (before after : list byte) (acc wordPointer wordLength : bv 64)
    (zero : Z) (pad bytes image : list byte) :
  bytes = nextUint64Le8 (bv_unsigned acc) ++
    [Z_to_bv 8 (Z.land zero (Z.ones 8)); Z_to_bv 8 (Z.land (Z.shiftr zero 8) (Z.ones 8))] ++ pad ->
  zero = 0 ->
  image = nextUint64Le8 (bv_unsigned (bv_add wordPointer (nextUint64ConsumedWord after))) ++
    nextUint64Le8 (bv_unsigned (bv_sub wordLength (nextUint64ConsumedWord after))) ->
  bv_unsigned wordPointer = nextInputPointer (nextUint64Base args) ->
  bv_unsigned wordLength = Z.of_nat (length (nextInputBytes (nextUint64Base args))) ->
  nextUint64BoundaryDomain args ->
  length after = 40%nat ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs argv sp inputEnd (nextInputBytes (nextUint64Base args)) before) after ->
  bv_unsigned (argv !!! 1%nat) = nextInputPointer (nextUint64Base args) ->
  bv_unsigned (nextUint64Status16Word after) = 0 ->
  bv_unsigned (nextUint64ListBitWord after) = 0 ->
  8 >= bv_unsigned (listWord64At8 after) ->
  bv_unsigned acc = zesu_byte_window_fold (nextInputBytes (nextUint64Base args))
    (Z.to_nat (bv_unsigned (listWord64At0 after) - nextInputPointer (nextUint64Base args)))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  length pad = 6%nat ->
  exists result : NextUint64Return,
    nextResultBytes result = bytes /\
    image = nextUint64SliceImage (nextRestPointer result) (nextRestLength result) /\
    nextUint64RootResult (nextUint64Base args) result.
Proof.
  intros -> -> -> Hwp Hwl Hdomain Hlen Hcall Hptr Hstatus Hbit Hlength Hfold Hpad.
  rewrite bv_add_unsigned, bv_sub_unsigned, Hwp, Hwl, nextUint64ConsumedWordValue
    by exact Hlen.
  rewrite nextUint64PointerWordValue, nextUint64LengthWordValue in Hfold by exact Hlen.
  rewrite nextUint64LengthWordValue in Hlength by exact Hlen.
  rewrite nextUint64StatusWordValue in Hstatus by exact Hlen.
  rewrite nextUint64ListBitWordValue in Hbit.
  pose proof (decodeItemCallMeaningLink _ _ Hcall) as Hlink.
  assert (Hptr' : decodeItemInputPointer
      (decodeItemCallDataArgs argv sp inputEnd (nextInputBytes (nextUint64Base args)) before) =
      nextInputPointer (nextUint64Base args))
    by (rewrite nextUint64CallInputPointer; exact Hptr).
  pose proof (nextUint64Accept
    (decodeItemCallDataArgs argv sp inputEnd (nextInputBytes (nextUint64Base args)) before)
    after _ eq_refl Hptr' Hlink Hstatus Hbit ltac:(Zify.zify; xlia Lia.zchecker)) as Haccept.
  pose proof (nextUint64DomainFits args Hdomain) as [Hp0 Hfit].
  unfold word64Modulus in Hfit.
  assert (Hconsumed : 0 <= nextUint64DecodedConsumed after <=
      Z.of_nat (length (nextInputBytes (nextUint64Base args)))).
  { destruct Haccept as (h & p & _ & Hh & Hp & Hle & _ & _ & _ & Hc & _).
    Zify.zify; xlia Lia.zchecker. }
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite !Z.mod_small by (Zify.zify; xlia Lia.zchecker).
  exists {| nextResultBytes := word64Bytes (bv_unsigned acc) ++ [BV 8 0; BV 8 0] ++ pad;
            nextRestPointer :=
              nextInputPointer (nextUint64Base args) + nextUint64DecodedConsumed after;
            nextRestLength :=
              Z.of_nat (length (nextInputBytes (nextUint64Base args))) -
                nextUint64DecodedConsumed after |}.
  split; [|split].
  - cbn [nextResultBytes]. rewrite nextUint64Le8Bytes.
    f_equal. cbn [app]. f_equal; [apply bv_eq; reflexivity|]. f_equal.
    apply bv_eq; reflexivity.
  - cbn [nextRestPointer nextRestLength]. unfold nextUint64SliceImage.
    rewrite !nextUint64Le8Bytes. reflexivity.
  - apply (nextUint64SuccessExitMeaning args after acc pad Hdomain); [|exact Hpad].
    split; [exact Haccept|]. rewrite Hfold. reflexivity.
Qed.

