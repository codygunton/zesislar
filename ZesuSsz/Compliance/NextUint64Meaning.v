(* The meaning conjunct of the nextUint64 contract (nextUint64RootResult), as
   pure lemmas over the history facts the exit blocks hold.

   Block addresses are offsets from the entry 0x800d6274:
   0x0064 (0x800d62d8) error exit, 0x00a4 (0x800d6318) loop head,
   0x00b8 (0x800d632c) success exit, both exits joining at the return
   0x0070 (0x800d62e4).

   History facts used (each premise below names the one it is):
   [call]     the decodeItem call record, through decodeItemCallMeaningLink as
              DecodeMeaningModuloKnownBugs, with the call's input bytes and
              input pointer equal to nextUint64's;
   [length]   length of the decodeItem output = 40 (inside the record);
   [domain]   nextUint64BoundaryDomain;
   [branch]   at 0x0064: the disjunction of the three branches that reach it;
   [accept]   on the success path: status 0, list bit clear, length <= 8;
   [invariant] at 0x00a4: nextUint64FoldInvariant over x12, x13, x11;
   [fold]     at 0x00b8: nextUint64FoldComplete over x11;
   [window]   the payload lies inside the input (loop start).
   The generated entries lacked [branch] (entry 0x0064), [invariant]
   (entry 0x00a4) and [fold] (entry 0x00b8) when measured; each lemma that
   needs one takes it as a named premise. The loop steps over [invariant]
   are in NextUint64MeaningLoop (they need NextUint64FoldFacts, which loads
   the legacy automation; block callers import this module through
   ZesuSsz.Contracts.NextUint64MeaningFacts and must not load it).

   The conversion from the entries' machine spellings (bv_concat chains of
   List.nth, bv_signed of a zero extension) to the views used here is done
   in ZesuSsz.Contracts.NextUint64MeaningFacts, which also registers the
   exits for the residual tier.

   Sail: rlp_decode_uint64 agrees with this meaning in one direction only
   (Sail success implies the same contract value). The code also accepts a
   leading zero (82 00 01) and zero written as 00, which Sail rejects; that
   is a registered known bug, not part of this module. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list list_numbers bitvector.definitions bitvector.tactics.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Interfaces.DecodeItem.
Import ListNotations.
Open Scope Z_scope.

(* The library solver, whatever an imported automation module made of
   [Lia.lia]. *)
Local Ltac library_lia := Zify.zify; xlia Lia.zchecker.

(* ---- byte views ---- *)
Lemma nextUint64SkipnNth (l : list byte) k x :
  nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH, H.
Qed.

Lemma nextUint64ByteAtNth (l : list byte) k v :
  byteAt l k v -> bv_unsigned (nth k l (BV 8 0)) = v.
Proof.
  unfold byteAt. destruct (nth_error l k) as [x|] eqn:E; cbn; [|discriminate].
  intros [= <-]. rewrite (nth_error_nth _ _ _ E). reflexivity.
Qed.

Lemma nextUint64StatusValue (l : list byte) a b :
  byteAt l 32 a -> byteAt l 33 b -> littleEndian (firstn 2 (skipn 32 l)) = a + 256 * b.
Proof.
  unfold byteAt. intros H32 H33.
  destruct (nth_error l 32) as [x|] eqn:E32; [|discriminate H32].
  destruct (nth_error l 33) as [y|] eqn:E33; [|discriminate H33].
  cbn in H32, H33. injection H32 as <-. injection H33 as <-.
  rewrite (nextUint64SkipnNth _ _ _ E32), (nextUint64SkipnNth _ _ _ E33).
  cbn. rewrite firstn_O. cbn. ring.
Qed.

(* Generic facts about the contract's [littleEndian]. *)
Lemma nextUint64LittleEndianRange (bytes : list byte) :
  0 <= littleEndian bytes < 2 ^ (8 * Z.of_nat (length bytes)).
Proof.
  induction bytes as [|b bytes IH]; cbn [littleEndian length]; [lia|].
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 256 in Hb.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *.
  rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma nextUint64LittleEndianMachineBytes count z :
  0 <= z < 2 ^ (8 * Z.of_nat count) ->
  littleEndian (bv_to_little_endian (Z.of_nat count) 8 z) = z.
Proof.
  revert z. induction count as [|count IH]; intros z Hz.
  - replace z with 0 by (simpl in Hz; lia).
    reflexivity.
  - rewrite Nat2Z.inj_succ.
    unfold bv_to_little_endian at 1.
    rewrite Z_to_little_endian_succ by lia.
    simpl.
    rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    rewrite Z_to_bv_small by
      (unfold bv_modulus; cbn; apply Z.mod_pos_bound; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 8) with 256.
    change (list_fmap Z (bv 8) (fun b => Z_to_bv 8 b)
      (Z_to_little_endian (Z.of_nat count) 8 (z / 256))) with
      (bv_to_little_endian (Z.of_nat count) 8 (z / 256)).
    rewrite IH.
    + rewrite Z.mod_eq by lia. lia.
    + split.
      * apply Z.div_pos; lia.
      * rewrite Nat2Z.inj_succ in Hz.
        replace (8 * (Z.of_nat count + 1)) with
            (8 * Z.of_nat count + 8) in Hz by lia.
        rewrite Z.pow_add_r in Hz by lia.
        change (2 ^ 8) with 256 in Hz.
        apply Z.div_lt_upper_bound; lia.
Qed.

Lemma nextUint64LittleEndianWord64 (v : Z) :
  0 <= v < 2 ^ 64 -> littleEndian (word64Bytes v) = v.
Proof.
  intros Hv. rewrite <- nextUint64Word64BytesEncoding.
  apply (nextUint64LittleEndianMachineBytes 8). exact Hv.
Qed.

(* ---- the candidate's header and payload bounds ---- *)
(* The case analysis on the header class is decodeItem's interface lemma
   decodeItemCandidateSuccessBounds. *)
Lemma nextUint64CandidateBounds input isList hl pl :
  candidateDecodeItem input = candidateSuccess isList hl pl ->
  0 <= hl <= 9 /\ (hl + pl) mod word64Modulus <= Z.of_nat (length input).
Proof.
  intros Hc. destruct (decodeItemCandidateSuccessBounds _ _ _ _ Hc) as (Hhl & Hfit & _).
  split; assumption.
Qed.

(* ---- decodeItem's result as seen by nextUint64's three branches ---- *)
(* Accept: status 0 (0x800d62b8), list bit clear (0x800d62c0), length <= 8
   (0x800d62cc). Premises: [call], then [accept]. *)
Lemma nextUint64Accept (ca : DecodeItemArgs) (after : list byte) (base : NextUint64Call) :
  decodeItemInputBytes ca = nextInputBytes base ->
  decodeItemInputPointer ca = nextInputPointer base ->
  DecodeMeaningModuloKnownBugs ca after ->
  nextUint64DecodedStatus after = 0 ->
  Z.land (bv_unsigned (nth 16 after (BV 8 0))) 1 = 0 ->
  nextUint64DecodedLength after <= 8 ->
  nextUint64AcceptedBytes base after.
Proof.
  intros Hin Hptr [HC _] Hst Htag Hlen.
  unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult in HC.
  destruct HC as (_ & H40 & _).
  unfold candidateResult40 in H40. rewrite Hin, Hptr in H40.
  unfold nextUint64DecodedStatus, nextUint64DecodedLength in *.
  destruct (candidateDecodeItem (nextInputBytes base)) as [|isList hl pl] eqn:Hc.
  - destruct H40 as [_ Hbytes].
    pose proof (Hbytes 32%nat ltac:(library_lia)) as H32.
    pose proof (Hbytes 33%nat ltac:(library_lia)) as H33. cbn in H32, H33.
    rewrite (nextUint64StatusValue _ _ _ H32 H33) in Hst. library_lia.
  - destruct H40 as (_ & Ha40 & Hp & Hl & Ht & Hc24 & H32 & H33 & _).
    rewrite (nextUint64ByteAtNth _ _ _ Ht) in Htag.
    destruct isList; [cbn in Htag; discriminate|].
    destruct Hl as [_ Hl]. destruct Hp as [_ Hp]. destruct Hc24 as [_ Hc24].
    rewrite Hl in Hlen.
    destruct (nextUint64CandidateBounds _ _ _ _ Hc) as [Hhl Hmod].
    assert (Hpl0 : 0 <= pl).
    { rewrite <- Hl. apply nextUint64LittleEndianRange. }
    unfold word64Modulus in Hmod, Hc24.
    rewrite Z.mod_small in Hmod, Hc24 by library_lia.
    exists hl, pl. unfold nextUint64DecodedPointer, nextUint64DecodedConsumed.
    cbn [skipn] in Hp.
    split_and!; try assumption; library_lia.
Qed.

(* Reject: any of the three branches to 0x800d62d8. Premises: [call],
   then [branch]. *)
Lemma nextUint64Reject (ca : DecodeItemArgs) (after : list byte) (base : NextUint64Call) :
  decodeItemInputBytes ca = nextInputBytes base ->
  decodeItemInputPointer ca = nextInputPointer base ->
  DecodeMeaningModuloKnownBugs ca after ->
  (nextUint64DecodedStatus after <> 0 \/
   Z.land (bv_unsigned (nth 16 after (BV 8 0))) 1 <> 0 \/
   8 < nextUint64DecodedLength after) ->
  nextUint64Rejects base.
Proof.
  intros Hin Hptr [HC _] Hbranch.
  unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult in HC.
  destruct HC as (_ & H40 & _).
  unfold candidateResult40 in H40. rewrite Hin, Hptr in H40.
  unfold nextUint64Rejects, nextUint64DecodedStatus, nextUint64DecodedLength in *.
  destruct (candidateDecodeItem (nextInputBytes base)) as [|isList hl pl] eqn:Hc; [exact I|].
  destruct H40 as (_ & _ & _ & Hl & Ht & _ & H32 & H33 & _).
  destruct Hbranch as [Hst | [Htag | Hlen]].
  - exfalso. rewrite (nextUint64StatusValue _ _ _ H32 H33) in Hst. library_lia.
  - left. rewrite (nextUint64ByteAtNth _ _ _ Ht) in Htag.
    destruct isList; [reflexivity|]. exfalso. apply Htag. reflexivity.
  - right. destruct Hl as [_ Hl]. library_lia.
Qed.

(* ---- the domain fit, then the two exits into the return join ---- *)
(* Premise: [domain]. *)
Lemma nextUint64DomainFits (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  inputAddressFits (nextInputPointer (nextUint64Base params))
    (nextInputBytes (nextUint64Base params)).
Proof.
  intros [Hlayout _]. unfold nextUint64EntryLayout in Hlayout.
  unfold inputAddressFits. library_lia.
Qed.

(* Error exit (block 0x800d62d8: sd zero,0(s1); sd 3,8(s1); slice untouched). *)
Definition nextUint64ErrorBytes : list byte := word64Bytes 0 ++ word64Bytes 3.

Lemma nextUint64ErrorResult (base : NextUint64Call) :
  inputAddressFits (nextInputPointer base) (nextInputBytes base) ->
  nextUint64Rejects base ->
  nextUint64RootResult base
    {| nextResultBytes := nextUint64ErrorBytes;
       nextRestPointer := nextInputPointer base;
       nextRestLength := Z.of_nat (length (nextInputBytes base)) |}.
Proof.
  intros Hfits Hrej. split; [exact Hfits|].
  assert (Herr : nextUint64Error16 nextUint64ErrorBytes).
  { unfold nextUint64Error16, word64At. vm_compute. split_and!; reflexivity. }
  unfold nextUint64Rejects in Hrej. cbn [nextResultBytes nextRestPointer nextRestLength].
  destruct (candidateDecodeItem (nextInputBytes base)) as [|isList hl pl]; [auto|].
  destruct Hrej as [-> | Hpl]; [cbn; auto|].
  destruct isList; cbn; [auto|].
  rewrite (proj2 (Z.ltb_lt 8 pl) Hpl). auto.
Qed.

(* Success exit (block 0x800d632c: slice := (ptr + consumed, len - consumed);
   result[0..8] := accumulator; result[8..10] := 0; result[10..16] unwritten). *)
Lemma nextUint64SuccessResult (base : NextUint64Call) (after : list byte) (acc : bv 64)
    (pad : list byte) :
  inputAddressFits (nextInputPointer base) (nextInputBytes base) ->
  nextUint64FoldComplete base after acc ->
  length pad = 6%nat ->
  nextUint64RootResult base
    {| nextResultBytes := word64Bytes (bv_unsigned acc) ++ [BV 8 0; BV 8 0] ++ pad;
       nextRestPointer := nextInputPointer base + nextUint64DecodedConsumed after;
       nextRestLength :=
         Z.of_nat (length (nextInputBytes base)) - nextUint64DecodedConsumed after |}.
Proof.
  intros Hfits [Hacc Hval] Hpad.
  destruct Hacc as (hl & pl & Hc & Hhl & Hpl & Hfit & _ & Hptr & Hlen & Hcons & _).
  split; [exact Hfits|]. cbn [nextResultBytes nextRestPointer nextRestLength].
  rewrite Hc. cbn [orb].
  replace (8 <? pl) with false by (symmetry; apply Z.ltb_ge; library_lia).
  rewrite Hcons. split; [|split; reflexivity].
  pose proof (bv_unsigned_in_range _ acc) as Hacc. unfold bv_modulus in Hacc.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Hacc.
  assert (Hpayload : nextUint64Payload base after =
    firstn (Z.to_nat pl) (skipn (Z.to_nat hl) (nextInputBytes base))).
  { unfold nextUint64Payload. rewrite Hlen, Hptr.
    destruct (nextInputBytes base) as [|p rest] eqn:Hinput; [discriminate|].
    destruct (bv_unsigned p =? 128) eqn:E128.
    - apply Z.eqb_eq in E128. cbn [candidateDecodeItem] in Hc. rewrite E128 in Hc.
      cbn in Hc. injection Hc as <- <-. reflexivity.
    - do 3 f_equal. library_lia. }
  unfold nextUint64Success16. split_and!.
  - rewrite !app_length, Hpad. unfold word64Bytes. rewrite map_length, seq_length. reflexivity.
  - unfold nextUint64ByteFold. split.
    + rewrite firstn_length. library_lia.
    + rewrite firstn_app. unfold word64Bytes at 2.
      rewrite map_length, seq_length, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (unfold word64Bytes; rewrite map_length, seq_length; library_lia).
      rewrite nextUint64LittleEndianWord64 by library_lia.
      rewrite Hval, Hpayload. reflexivity.
  - unfold byteAt. reflexivity.
  - unfold byteAt. reflexivity.
Qed.

(* Exit lemma of entry 0x0064 into the return 0x0070. Premises: [domain],
   [call], [branch]. [branch] must be supplied by the generated entry 0x0064
   (the disjunction of its incoming edges' guards). *)
Lemma nextUint64ErrorExitMeaning (params : NextUint64Args) (ca : DecodeItemArgs)
    (after : list byte) :
  nextUint64BoundaryDomain params ->
  decodeItemInputBytes ca = nextInputBytes (nextUint64Base params) ->
  decodeItemInputPointer ca = nextInputPointer (nextUint64Base params) ->
  DecodeMeaningModuloKnownBugs ca after ->
  forall (Hbranch : nextUint64DecodedStatus after <> 0 \/
    Z.land (bv_unsigned (nth 16 after (BV 8 0))) 1 <> 0 \/
    8 < nextUint64DecodedLength after),
  nextUint64RootResult (nextUint64Base params)
    {| nextResultBytes := nextUint64ErrorBytes;
       nextRestPointer := nextInputPointer (nextUint64Base params);
       nextRestLength := Z.of_nat (length (nextInputBytes (nextUint64Base params))) |}.
Proof.
  intros Hdomain Hin Hptr Hcall Hbranch.
  apply nextUint64ErrorResult.
  - exact (nextUint64DomainFits params Hdomain).
  - exact (nextUint64Reject ca after _ Hin Hptr Hcall Hbranch).
Qed.

(* Exit lemma of entry 0x00b8 into the return 0x0070. Premises: [domain],
   [fold]. [fold] must be supplied by the generated entry 0x00b8 (the fold
   result over x11, from nextUint64FoldLast at 0x00a4 or nextUint64EmptyFold
   at 0x0090). *)
Lemma nextUint64SuccessExitMeaning (params : NextUint64Args) (after : list byte)
    (acc : bv 64) (pad : list byte) :
  nextUint64BoundaryDomain params ->
  forall (Hfold : nextUint64FoldComplete (nextUint64Base params) after acc),
  length pad = 6%nat ->
  nextUint64RootResult (nextUint64Base params)
    {| nextResultBytes := word64Bytes (bv_unsigned acc) ++ [BV 8 0; BV 8 0] ++ pad;
       nextRestPointer :=
         nextInputPointer (nextUint64Base params) + nextUint64DecodedConsumed after;
       nextRestLength :=
         Z.of_nat (length (nextInputBytes (nextUint64Base params))) -
           nextUint64DecodedConsumed after |}.
Proof.
  intros Hdomain Hfold Hpad.
  exact (nextUint64SuccessResult _ after acc pad
    (nextUint64DomainFits params Hdomain) Hfold Hpad).
Qed.

(* ---- the loop body's machine step is the contract's fold step ---- *)
(* 0x800d631c slli a1,a1,8; 0x800d6324 or a1,a1,a4 (a4 = lbu). *)
Lemma nextUint64LorShiftByte (a b : Z) :
  0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
  intros Hb. symmetry. apply Z.add_nocarry_lor.
  rewrite <- (Z.mod_small b 256) by exact Hb.
  change 256 with (2 ^ 8).
  rewrite <- (Z.land_ones b 8) by library_lia.
  rewrite (Z.land_comm b (Z.ones 8)), Z.land_assoc, (Z.land_ones (a * 2 ^ 8) 8)
    by library_lia.
  rewrite Z.mod_mul by library_lia.
  apply Z.land_0_l.
Qed.

Lemma nextUint64ShiftOrStep (acc : bv 64) (b : bv 8) :
  bv_or (bv_shiftl acc (BV 64 8)) (bv_zero_extend 64 b) =
  Z_to_bv 64 (bv_unsigned acc * 256 + bv_unsigned b).
Proof.
  apply bv_eq.
  rewrite bv_or_unsigned, bv_shiftl_unsigned, Z_to_bv_unsigned.
  rewrite (bv_zero_extend_unsigned 64 b) by library_lia.
  change (bv_unsigned (BV 64 8)) with 8.
  rewrite Z.shiftl_mul_pow2 by library_lia. change (2 ^ 8) with 256.
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  set (a := bv_unsigned acc). set (c := bv_unsigned b).
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (72057594037927936 * 256).
  rewrite <- (Z.add_mod_idemp_l (a * 256) c) by library_lia.
  rewrite Z.mul_mod_distr_r by library_lia.
  pose proof (Z.mod_pos_bound a 72057594037927936 ltac:(library_lia)) as Ha.
  rewrite nextUint64LorShiftByte by exact Hb.
  rewrite (Z.mod_small (a mod 72057594037927936 * 256 + c)) by library_lia.
  reflexivity.
Qed.

(* With the accumulator below 2^56 the machine value is the exact fold. *)
Lemma nextUint64ShiftOrValue (acc : bv 64) (b : bv 8) :
  bv_unsigned acc < 2 ^ 56 ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8)) (bv_zero_extend 64 b)) =
    256 * bv_unsigned acc + bv_unsigned b.
Proof.
  intros Hacc. rewrite nextUint64ShiftOrStep, Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ acc) as Ha. pose proof (bv_unsigned_in_range _ b) as Hb.
  unfold bv_modulus in Ha, Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  change (2 ^ 56) with 72057594037927936 in Hacc.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_small by library_lia. library_lia.
Qed.

