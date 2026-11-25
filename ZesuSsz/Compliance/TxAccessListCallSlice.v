From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.DecodeItemCallFacts.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Contracts.DecodeItemCallSlice.
Import ListNotations.
Local Open Scope Z_scope.

(* txAccessList calls decodeItem on windows of its input with 40-byte
   output slots inside its own 576-byte frame; the callee's stack pointer is
   the frame base, its 16 bytes lie in the 128 callee bytes below. *)
Lemma txAccessListDecodeItemCallDomain (args : TxAccessListArgs) (p l out sp : bv 64) (k : Z)
    (rest : list (bv 64)) (before : list byte) :
  txAccessListArgsWellFormed args ->
  (bv_unsigned (txInputPointer args) <= bv_unsigned p /\
   bv_unsigned p + bv_unsigned l <= bv_unsigned (txInputPointer args) +
     Z.of_nat (length (txInputBytes args))) ->
  bv_unsigned sp = bv_unsigned (txStackPointer args) - 576 ->
  bv_unsigned out = bv_unsigned (txStackPointer args) - 576 + k ->
  0 <= k <= 536 ->
  length before = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs (out :: p :: l :: rest)
    sp (bv_unsigned (txInputEnd args))
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (txInputPointer args)))
        (txInputBytes args)))
    before).
Proof.
  intros Hwf [Hlo Hhi] Hsp Hout Hk Hbefore.
  apply decodeItemCallDomainIntro.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed, decodeItemEntryLayout, separateRanges,
    decodeItemCallDataArgs.
  cbn.
  destruct Hwf as (Hr & Hlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsep & _).
  unfold txAccessListArgsRanges in Hr. unfold txAccessListCalleeBase, separateRanges in Hsep.
  rewrite length_take, length_drop, Hsp, Hout.
  pose proof (bv_unsigned_in_range _ l) as Hl.
  pose proof (bv_unsigned_in_range _ p) as Hp.
  pose proof (bv_unsigned_in_range _ (txInputEnd args)) as He.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616.
  change (2 ^ 30) with 1073741824 in *.
  change (2 ^ 31) with 2147483648 in *.
  repeat split; first [exact Hbefore | lia].
Qed.

#[export] Instance txAccessListDecodeItemCallSlice :
  ZesuCallSliceCaller txAccessListArgsWellFormed decodeItemCallSliceInterface
    (fun args => bv_unsigned (txInputPointer args))
    (fun args => txInputBytes args)
    (fun args => bv_unsigned (txStackPointer args) - 576)
    (fun args => bv_unsigned (txInputEnd args))
    536.
Proof.
  intros args p l out sp k ie rest before Hwf Hwin Hsp Hout Hk -> Hbefore.
  exact (txAccessListDecodeItemCallDomain args p l out sp k rest before
    Hwf Hwin Hsp Hout Hk Hbefore).
Qed.

(* The first decodeItem call reads the whole input: its header fits (the
   domain's first reached call), so the payload length it returns is at most
   the input length. *)
Lemma txAccessListInputHeaderFits (args : TxAccessListArgs) :
  txAccessListArgsWellFormed args -> headerFits (txInputBytes args).
Proof.
  intros Hwf. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [Hfit _]).
  assert (Hhead : exists calls, accessListCalls (txInputBytes args) =
    (accessListOuterCall, txInputBytes args) :: calls).
  { unfold accessListCalls, accessListWalk. repeat case_match; eexists; reflexivity. }
  destruct Hhead as [calls Hcalls]. unfold accessListHeadersFit in Hfit.
  rewrite Hcalls in Hfit. by inversion Hfit.
Qed.

Lemma txAccessListOuterPayloadBound (args : TxAccessListArgs) (argv : list (bv 64))
    (sp : bv 64) (inputEnd : Z) (before after : list byte) :
  txAccessListArgsWellFormed args ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs argv sp inputEnd (txInputBytes args) before) after ->
  bv_unsigned (listWord64At8 after) < 18446744073709551607.
Proof.
  intros Hwf Hmeaning.
  pose proof (decodeItemCallPayloadFits _ _ _ _ _ _ Hmeaning (txAccessListInputHeaderFits args Hwf)) as Hp.
  destruct Hwf as (Hr & Hlen & _).
  unfold txAccessListArgsRanges in Hr.
  pose proof (bv_unsigned_in_range _ (txInputPointer args)).
  change (2 ^ 30) with 1073741824 in *. change (2 ^ 31) with 2147483648 in *.
  assert (Hn : Z.of_nat (length (txInputBytes args)) <= 3221225472) by lia.
  (* Hp states the length at the interface's element type: convertible, not
     syntactically equal, so `lia` alone sees two atoms. *)
  eapply Z.le_lt_trans; [exact Hp|].
  eapply Z.le_lt_trans; [exact Hn|].
  lia.
Qed.

#[export] Instance txAccessListDecodeItemPayloadBound :
  ZesuCallSliceCallerPayloadBound txAccessListArgsWellFormed decodeItemCallSliceInterface
    (fun args => txInputBytes args).
Proof.
  intros args argv sp ie before after Hwf Hmeaning.
  exact (txAccessListOuterPayloadBound args argv sp ie before after Hwf Hmeaning).
Qed.

(* The outer loop's cursor window: the cursor has walked i bytes of the
   payload the first call returned and l bytes are left. *)
Lemma txAccessListOuterWindow (args : TxAccessListArgs) (out sp : bv 64) (rest : list (bv 64))
    (inputEnd : Z) (before after : list byte) (p l : bv 64) (i : Z) :
  txAccessListArgsWellFormed args ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs (out :: txInputPointer args :: rest) sp inputEnd
      (txInputBytes args) before) after ->
  bv_unsigned p = bv_unsigned (listWord64At0 after) + i ->
  0 <= i ->
  bv_unsigned l + i = bv_unsigned (listWord64At8 after) ->
  0 < bv_unsigned l ->
  bv_unsigned (txInputPointer args) <= bv_unsigned p /\
  bv_unsigned p + bv_unsigned l <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)).
Proof.
  intros Hwf Hmeaning Hp Hi Hl Hpos.
  pose proof (txAccessListOuterPayloadBound args _ _ _ _ _ Hwf Hmeaning) as Hbound.
  assert (Hlen : 0 < bv_unsigned (listWord64At8 after)) by lia.
  destruct (decodeItemCallPayloadInInput _ _ _ _ _ _ _ _ Hmeaning Hlen Hbound)
    as [Hlo Hhi].
  (* the interface's words are the same terms at its own element type *)
  change (bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args))) in Hhi.
  change (bv_unsigned (txInputPointer args) <= bv_unsigned (listWord64At0 after)) in Hlo.
  lia.
Qed.

(* The plain ranges of the entry domain as linear facts. The contract
   registers `txAccessListArgsRanges` folded (TxAccessListContract.v), which
   the solvers do not open; the call-site step's address side conditions
   (`CallSlice.zesu_call_slice_address`) read the stack pointer's range from
   here. The alignment of the allocator pointer is left out (a symbolic
   divisibility makes every failing `lia` branch). *)
#[export] Instance txAccessListArgsRangesPlain (args : TxAccessListArgs) :
  ZesuDomainRanges (txAccessListArgsRanges args)
    ((2684354560 <= bv_unsigned (txResultPointer args) /\
      bv_unsigned (txResultPointer args) + 24 <= 3221225472) /\
     (2684354560 <= bv_unsigned (txAllocatorPointer args) /\
      bv_unsigned (txAllocatorPointer args) + 16 <= 3221225472) /\
     (2684354560 <= bv_unsigned (txRestPointer args) /\
      bv_unsigned (txRestPointer args) + 16 <= 3221225472) /\
     (2684355264 <= bv_unsigned (txStackPointer args) /\
      bv_unsigned (txStackPointer args) <= 3221225472) /\
     bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
       bv_unsigned (txInputEnd args) /\
     ((1073741824 <= bv_unsigned (txInputPointer args) /\
       bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <= 2147483648) \/
      (2684354560 <= bv_unsigned (txInputPointer args) /\
       bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <= 3221225472))).
Proof.
  intros H. unfold txAccessListArgsRanges in H.
  change (2 ^ 30) with 1073741824 in H. change (2 ^ 31) with 2147483648 in H.
  lia.
Qed.

(* The payload of a call that returned a list lies inside that call's input,
   even when it is empty: a list result is a success (an error clears byte
   16), its prefix is at least 0xc0, so the payload starts after the header,
   and the header fits, so header and payload do not wrap 2^64. The entry
   loop calls decodeItem on the entry's payload with no length test
   (+0xec..+0x108), so an empty entry (0xc0) reaches that call. *)
Lemma txAccessListListPayloadWindow (argv0 q : bv 64) (rest : list (bv 64)) (sp : bv 64)
    (inputEnd : Z) (input before after : list byte) :
  decodeItemCallMeaning (decodeItemCallDataArgs (argv0 :: q :: rest) sp inputEnd input before) after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  headerFits input ->
  bv_unsigned q <= bv_unsigned (leWord64 after 0) /\
  bv_unsigned (leWord64 after 0) + bv_unsigned (leWord64 after 8) <=
    bv_unsigned q + Z.of_nat (length input).
Proof.
  intros Hm Hlist Hfits.
  pose proof (decodeItemMeaningC1B _ _ (decodeItemCallMeaningLink _ _ Hm)) as Hc1b.
  cbn [decodeItemCallDataArgs decodeItemInputPointer decodeItemInputBytes
       decodeItemBeforeStorage] in Hc1b.
  change ((argv0 :: q :: rest) !!! 1%nat) with q in Hc1b.
  unfold C1BResult, candidateResult40 in Hc1b. destruct Hc1b as (_ & Hres & _).
  assert (Hbit : forall b : byte, bv_unsigned b = 0 ->
            bv_unsigned (bv_and (bv_zero_extend 64 b) (BV 64 1)) = 0).
  { intros b Hb. rewrite bv_and_unsigned, bv_zero_extend_unsigned. { rewrite Hb. reflexivity. } done. }
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - exfalso. apply Hlist, Hbit. destruct Hres as [_ Hb].
    exact (byteAtNth _ _ _ (Hb 16%nat ltac:(lia))).
  - destruct Hres as (_ & _ & H0 & H8 & H16 & _).
    pose proof (candidateDecodeItemFitsNoWrap _ _ _ _ Hfits Hc) as Hnw.
    destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hin & _).
    rewrite (leWord64Value _ _ _ H8).
    destruct input as [|prefix tail]; [discriminate|].
    destruct isList; cycle 1.
    { exfalso. apply Hlist, Hbit. exact (byteAtNth _ _ _ H16). }
    assert (Hpre : bv_unsigned prefix <> 128).
    { intros E. unfold candidateDecodeItem in Hc. rewrite E in Hc. discriminate. }
    rewrite (proj2 (Z.eqb_neq _ _) Hpre) in H0.
    rewrite (leWord64Value _ _ _ H0).
    assert (Hp : 0 <= p) by (destruct H8 as [_ <-]; apply littleEndianRange).
    unfold word64Modulus in *. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite Z.mod_small in Hin by lia.
    pose proof (bv_unsigned_in_range _ q). lia.
Qed.

(* A load the block computes reads the outcome at the element type `bv 8`
   (`take`/`drop` at `bv 8`), not at `byte`: the call step matches the window
   facts syntactically, so they are stated in that spelling. *)
Local Notation leWord64Bits bytes offset :=
  (Z_to_bv 64 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 8) (@drop (bv 8) offset bytes))))
  (only parsing).

(* The same window over the caller's whole input, for a call on the window
   [p, p + l) of it (the entry call at +0xc4 on the cursor window). *)
Lemma txAccessListListPayloadInInput (args : TxAccessListArgs) (argv0 p l : bv 64)
    (rest : list (bv 64)) (sp : bv 64) (inputEnd : Z) (before after : list byte) :
  let window := take (Z.to_nat (bv_unsigned l))
    (drop (Z.to_nat (bv_unsigned p - bv_unsigned (txInputPointer args))) (txInputBytes args)) in
  decodeItemCallMeaning (decodeItemCallDataArgs (argv0 :: p :: l :: rest) sp inputEnd window before) after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  headerFits window ->
  bv_unsigned (txInputPointer args) <= bv_unsigned p ->
  bv_unsigned p + bv_unsigned l <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)) ->
  bv_unsigned (txInputPointer args) <= bv_unsigned (leWord64Bits after 0) /\
  bv_unsigned (leWord64Bits after 0) + bv_unsigned (leWord64Bits after 8) <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)).
Proof.
  intros window Hm Hlist Hfits Hlo Hhi.
  destruct (txAccessListListPayloadWindow _ _ _ _ _ _ _ _ Hm Hlist Hfits) as [H1 H2].
  change (leWord64Bits after 0) with (leWord64 after 0).
  change (leWord64Bits after 8) with (leWord64 after 8).
  subst window. rewrite length_take, length_drop in H2.
  set (w0 := bv_unsigned (leWord64 after 0)) in *.
  set (w8 := bv_unsigned (leWord64 after 8)) in *.
  pose proof (bv_unsigned_in_range _ l). lia.
Qed.

(* A successful call's payload ends inside the call's input: the error code
   (bytes 32 and 33) is zero only for a success (an error writes 4 at byte
   32); the payload pointer is the input pointer plus the header length, or 1
   with no payload for the empty string 0x80, and the header fits, so header
   and payload do not wrap 2^64. Stated over the byte concatenations the
   generator renders for the loads of words 0 and 8. *)
Lemma txAccessListSuccessPayloadWindow (argv0 q : bv 64) (rest : list (bv 64)) (sp : bv 64)
    (inputEnd : Z) (input before after : list byte) :
  decodeItemCallMeaning (decodeItemCallDataArgs (argv0 :: q :: rest) sp inputEnd input before) after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  headerFits input ->
  1 <= bv_unsigned q ->
  bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned q + Z.of_nat (length input).
Proof.
  intros Hm Hcode Hfits Hq.
  rewrite concatByteUnsigned in Hcode by reflexivity.
  pose proof (bv_unsigned_in_range _ (List.nth 33 after (BV 8 0))) as H33.
  pose proof (bv_unsigned_in_range _ (List.nth 32 after (BV 8 0))) as H32.
  unfold bv_modulus in H33, H32.
  pose proof (decodeItemMeaningC1B _ _ (decodeItemCallMeaningLink _ _ Hm)) as Hc1b.
  cbn [decodeItemCallDataArgs decodeItemInputPointer decodeItemInputBytes
       decodeItemBeforeStorage] in Hc1b.
  change ((argv0 :: q :: rest) !!! 1%nat) with q in Hc1b.
  unfold C1BResult, candidateResult40 in Hc1b. destruct Hc1b as (_ & Hres & _).
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - exfalso. destruct Hres as [_ Hb].
    pose proof (byteAtNth _ _ _ (Hb 32%nat ltac:(lia))) as H4. cbn in H4. lia.
  - destruct Hres as (_ & _ & H0 & H8 & _).
    pose proof (candidateDecodeItemFitsNoWrap _ _ _ _ Hfits Hc) as Hnw.
    destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hin & H128).
    rewrite (listWord64At8Value _ _ H8), (listWord64At0Value _ _ H0).
    assert (Hp : 0 <= p) by (destruct H8 as [_ <-]; apply littleEndianRange).
    unfold word64Modulus in *. change (2 ^ 64) with 18446744073709551616 in *.
    rewrite Z.mod_small in Hin by lia.
    destruct input as [|prefix tail]; [discriminate|].
    destruct (Z.eqb_spec (bv_unsigned prefix) 128) as [E|E].
    + rewrite (H128 prefix tail eq_refl E). lia.
    + lia.
Qed.

(* The same over the caller's whole input, for a call on the window
   [p, p + l) of it (the item calls of the entry loop, +0x10c and +0x1a0). *)
Lemma txAccessListSuccessPayloadInInput (args : TxAccessListArgs) (argv0 p l : bv 64)
    (rest : list (bv 64)) (sp : bv 64) (inputEnd : Z) (before after : list byte) :
  let window := take (Z.to_nat (bv_unsigned l))
    (drop (Z.to_nat (bv_unsigned p - bv_unsigned (txInputPointer args))) (txInputBytes args)) in
  decodeItemCallMeaning (decodeItemCallDataArgs (argv0 :: p :: l :: rest) sp inputEnd window before) after ->
  headerFits window ->
  txAccessListArgsRanges args ->
  bv_unsigned (txInputPointer args) <= bv_unsigned p ->
  bv_unsigned p + bv_unsigned l <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)) ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)).
Proof.
  intros window Hm Hfits Hranges Hlo Hhi Hcode.
  pose proof (txAccessListArgsRangesPlain args Hranges) as Hplain.
  assert (Hq : 1 <= bv_unsigned p) by lia.
  pose proof (txAccessListSuccessPayloadWindow _ _ _ _ _ _ _ _ Hm Hcode Hfits Hq) as H.
  subst window. rewrite length_take, length_drop in H.
  set (w0 := bv_unsigned (listWord64At0 after)) in *.
  set (w8 := bv_unsigned (listWord64At8 after)) in *.
  pose proof (bv_unsigned_in_range _ l). lia.
Qed.

(* The outer cut's walk fact on its entry from +0xac: the first call on the
   whole input returned a list (byte 16 set, so a success, prefix at least
   0xc0), its payload pointer is the input pointer plus the header length, so
   the cursor offset is the header length, and with no entry walked the walk
   of the payload is the walk of the whole rest. *)
Lemma txAccessListOuterWalkedStart (args : TxAccessListArgs) (argv0 : bv 64)
    (rest : list (bv 64)) (sp : bv 64) (inputEnd : Z) (before after : list byte) :
  decodeItemCallMeaning
    (decodeItemCallDataArgs (argv0 :: txInputPointer args :: rest) sp inputEnd
      (txInputBytes args) before) after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  txAccessListOuterWalked (txInputBytes args)
    (bv_unsigned (listWord64At0 after) - bv_unsigned (txInputPointer args)) [].
Proof.
  intros Hm Hlist.
  pose proof (decodeItemMeaningC1B _ _ (decodeItemCallMeaningLink _ _ Hm)) as Hc1b.
  cbn [decodeItemCallDataArgs decodeItemInputPointer decodeItemInputBytes
       decodeItemBeforeStorage] in Hc1b.
  change ((argv0 :: txInputPointer args :: rest) !!! 1%nat) with (txInputPointer args) in Hc1b.
  unfold C1BResult, candidateResult40 in Hc1b. destruct Hc1b as (_ & Hres & _).
  assert (Hbit : forall b : byte, bv_unsigned b = 0 ->
            bv_unsigned (bv_and (bv_zero_extend 64 b) (BV 64 1)) = 0).
  { intros b Hb. rewrite bv_and_unsigned, bv_zero_extend_unsigned. { rewrite Hb. reflexivity. } done. }
  destruct (candidateDecodeItem (txInputBytes args)) as [|isList h p] eqn:Hc.
  - exfalso. apply Hlist, Hbit. destruct Hres as [_ Hb].
    exact (byteAtNth _ _ _ (Hb 16%nat ltac:(lia))).
  - destruct Hres as (_ & _ & H0 & H8 & H16 & _).
    destruct isList; cycle 1.
    { exfalso. apply Hlist, Hbit. exact (byteAtNth _ _ _ H16). }
    assert (Hp : 0 <= p) by (destruct H8 as [_ <-]; apply littleEndianRange).
    destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & _ & _).
    assert (Hptr : bv_unsigned (listWord64At0 after) =
                   bv_unsigned (txInputPointer args) + h).
    { rewrite (listWord64At0Value _ _ H0).
      destruct (txInputBytes args) as [|prefix tail] eqn:Hin; [discriminate|].
      assert (Hpre : bv_unsigned prefix <> 128).
      { intros E. unfold candidateDecodeItem in Hc. rewrite E in Hc. discriminate. }
      rewrite (proj2 (Z.eqb_neq _ _) Hpre). reflexivity. }
    rewrite Hptr. exists h, p. split; [exact Hc|]. split; [lia|].
    cbn zeta. replace (bv_unsigned (txInputPointer args) + h - bv_unsigned (txInputPointer args) - h)
      with 0 by lia.
    cbn [Z.to_nat skipn app].
    destruct (snd _); reflexivity.
Qed.

Lemma txAccessListByteOfShift (x : Z) (k : nat) :
  Z_to_bv 8 (Z.land (Nat.iter k (fun y => Z.shiftr y 8) x) (Z.ones 8)) =
  Z_to_bv 8 (Z.shiftr x (8 * Z.of_nat k)).
Proof.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. f_equal.
  induction k as [|k IH]; [cbn; rewrite Z.shiftr_0_r; reflexivity|].
  rewrite Nat.iter_succ, IH, Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

(* The outer cut's entry from +0x7c: the first call on the whole input
   returned a list (byte 16 set) with an empty payload (word 8 is 0), so the
   walk is done at the end of the item, and the rest slot holds the input
   window after the item: pointer + consumed and length - consumed, with
   consumed the call's word 24. *)
Lemma txAccessListOuterEmptyPayload (args : TxAccessListArgs) (argv0 : bv 64)
    (rest : list (bv 64)) (sp : bv 64) (inputEnd : Z) (before after : list byte) :
  decodeItemCallMeaning
    (decodeItemCallDataArgs (argv0 :: txInputPointer args :: rest) sp inputEnd
      (txInputBytes args) before) after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 8 after))) = 0%bv ->
  Z.of_nat (length (txInputBytes args)) = bv_unsigned (txInputLength args) ->
  bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) < 2 ^ 64 ->
  let consumed := Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 24 after))) in
  let start := bv_unsigned (txInputPointer args + consumed) in
  let left := bv_unsigned (txInputLength args - consumed) in
  exists headerLength payloadLength,
    candidateDecodeItem (txInputBytes args) = candidateSuccess true headerLength payloadLength /\
    txAccessListOuterWalked (txInputBytes args) (headerLength + payloadLength) [] /\
    [Z_to_bv 8 (Z.land start (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr start 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr start 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr start 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr start 8) 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr start 8) 8) 8) 8) 8)
       (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr start 8) 8)
       8) 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
       (Z.shiftr start 8) 8) 8) 8) 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land left (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr left 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr left 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr left 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr left 8) 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr left 8) 8) 8) 8) 8)
       (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr left 8) 8)
       8) 8) 8) 8) (Z.ones 8));
     Z_to_bv 8 (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
       (Z.shiftr left 8) 8) 8) 8) 8) 8) 8) (Z.ones 8))] =
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 0)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 1)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 2)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 3)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 4)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 5)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 6)) ::
    Z_to_bv 8 (Z.shiftr (bv_unsigned (txInputPointer args) + (headerLength + payloadLength))
      (8 * Z.of_nat 7)) ::
    word64Bytes (bv_unsigned (txInputLength args) - (headerLength + payloadLength)).
Proof.
  intros Hm Hlist Hzero Hlen Hfit consumed start left.
  change (N.to_nat 8) with 8%nat in *.
  pose proof (decodeItemMeaningC1B _ _ (decodeItemCallMeaningLink _ _ Hm)) as Hc1b.
  cbn [decodeItemCallDataArgs decodeItemInputPointer decodeItemInputBytes
       decodeItemBeforeStorage] in Hc1b.
  unfold C1BResult, candidateResult40 in Hc1b. destruct Hc1b as (_ & Hres & _).
  assert (Hbit : forall b : byte, bv_unsigned b = 0 ->
            bv_unsigned (bv_and (bv_zero_extend 64 b) (BV 64 1)) = 0).
  { intros b Hb. rewrite bv_and_unsigned, bv_zero_extend_unsigned. { rewrite Hb. reflexivity. } done. }
  destruct (candidateDecodeItem (txInputBytes args)) as [|isList h p] eqn:Hc.
  { exfalso. apply Hlist, Hbit. destruct Hres as [_ Hb].
    exact (byteAtNth _ _ _ (Hb 16%nat ltac:(lia))). }
  destruct Hres as (_ & Hafter & _ & [_ H8] & H16 & [_ H24] & _).
  destruct isList; cycle 1.
  { exfalso. apply Hlist, Hbit. exact (byteAtNth _ _ _ H16). }
  destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hfits & _).
  (* the payload length is word 8, which is 0 *)
  assert (Hp : p = 0).
  { rewrite <- H8. rewrite <- littleEndianBv.
    pose proof (littleEndianRange (firstn 8 (skipn 8 after))) as Hr.
    rewrite <- littleEndianBv in Hr.
    apply (f_equal bv_unsigned) in Hzero.
    cbn [N.to_nat Pos.to_nat] in Hzero. rewrite Z_to_bv_small in Hzero.
    - exact Hzero.
    - unfold bv_modulus. cbn [Z.of_N].
      rewrite firstn_length_le in Hr; [|rewrite skipn_length, Hafter; lia].
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hr. lia. }
  clear H8. subst p. replace (h + 0) with h in * by lia.
  rewrite Z.mod_small in Hfits, H24 by (unfold word64Modulus in *; lia).
  assert (Hconsumed : bv_unsigned consumed = h).
  { unfold consumed. cbn [N.to_nat Pos.to_nat]. rewrite littleEndianBv, H24.
    apply Z_to_bv_small. unfold bv_modulus. lia. }
  assert (Hhl : h <= bv_unsigned (txInputLength args)) by (rewrite <- Hlen; exact Hfits).
  pose proof (bv_unsigned_in_range _ (txInputPointer args)) as Hpr.
  pose proof (bv_unsigned_in_range _ (txInputLength args)) as Hlr.
  unfold bv_modulus in Hpr, Hlr.
  assert (Hstart : start = bv_unsigned (txInputPointer args) + h).
  { unfold start. rewrite bv_add_unsigned, Hconsumed. apply bv_wrap_small.
    unfold bv_modulus. split; [lia|]. eapply Z.le_lt_trans; [|exact Hfit]. lia. }
  assert (Hleft : left = bv_unsigned (txInputLength args) - h).
  { unfold left. rewrite bv_sub_unsigned, Hconsumed. apply bv_wrap_small.
    unfold bv_modulus. split; [lia|]. eapply Z.le_lt_trans; [|exact Hfit]. lia. }
  exists h, 0. rewrite Z.add_0_r. split; [first [exact Hc | reflexivity]|]. split.
  - exists h, 0. split; [first [exact Hc | reflexivity]|]. split; [lia|]. cbn zeta.
    replace (h - h) with 0 by lia. cbn [Z.to_nat skipn].
    destruct (snd _); reflexivity.
  - rewrite Hstart, Hleft. unfold word64Bytes. cbn [List.map List.seq].
    repeat (apply (f_equal2 cons); [first
      [ exact (txAccessListByteOfShift _ 0)
      | exact (txAccessListByteOfShift _ 1) | exact (txAccessListByteOfShift _ 2)
      | exact (txAccessListByteOfShift _ 3) | exact (txAccessListByteOfShift _ 4)
      | exact (txAccessListByteOfShift _ 5) | exact (txAccessListByteOfShift _ 6)
      | exact (txAccessListByteOfShift _ 7) ] |]); reflexivity.
Qed.

(* The error exits after the outer header (join 0x4a8) store the rest pointer
   and length advanced by `h + p`; the outcome's allowed advance is
   `itemConsumed h p = (h + p) mod 2^64`. The stored bytes are the same: a
   byte below bit 64 of a sum depends on the sum modulo 2^64 only. *)
Lemma txAccessListByteModWord (x y : Z) (k : nat) :
  x mod 2 ^ 64 = y mod 2 ^ 64 -> (k < 8)%nat ->
  Z_to_bv 8 (Z.shiftr x (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr y (8 * Z.of_nat k)).
Proof.
  intros Hxy Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.ltb_spec i 8) as [Hlt|Hge].
  - rewrite <- (Z.mod_pow2_bits_low x 64 (i + 8 * Z.of_nat k)) by lia.
    rewrite <- (Z.mod_pow2_bits_low y 64 (i + 8 * Z.of_nat k)) by lia.
    rewrite Hxy. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma txAccessListByteConsumed (P h p : Z) (k : nat) :
  (k < 8)%nat ->
  Z_to_bv 8 (Z.shiftr (P + (h + p)) (8 * Z.of_nat k)) =
  Z_to_bv 8 (Z.shiftr (P + itemConsumed h p) (8 * Z.of_nat k)).
Proof.
  intros Hk. apply txAccessListByteModWord; [|exact Hk].
  unfold itemConsumed. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma txAccessListRestWordConsumed (L h p : Z) :
  AbiBytes.word64Bytes (L - (h + p)) = AbiBytes.word64Bytes (L - itemConsumed h p).
Proof.
  unfold AbiBytes.word64Bytes. cbn [List.seq List.map].
  assert (Hm : (L - (h + p)) mod 2 ^ 64 = (L - itemConsumed h p) mod 2 ^ 64).
  { unfold itemConsumed. rewrite Zminus_mod_idemp_r. reflexivity. }
  repeat (apply (f_equal2 cons); [apply txAccessListByteModWord; [exact Hm | lia] |]).
  reflexivity.
Qed.

Lemma txAccessListAllocationFailureItem (input : list byte) (h p : Z) :
  candidateDecodeItem input = candidateSuccess true h p -> 0 < p ->
  txAccessListOutcomeAllowed input txAccessListAllocationFailure (itemConsumed h p).
Proof. intros Hc Hp. exists h, p. auto. Qed.

(* The error-exit rest existential of the join-4a8 entry: witness the
   allowed advance, its stored bytes equal those of `h + p`. *)
Ltac txAccessListErrorExitRest :=
  lazymatch goal with
  | Hc : candidateDecodeItem _ = candidateSuccess true ?h ?p |- ex _ =>
      exists (itemConsumed h p); split;
      [ rewrite txAccessListRestWordConsumed;
        repeat (apply (f_equal2 cons); [apply txAccessListByteConsumed; lia |]);
        reflexivity
      | right; apply txAccessListAllocationFailureItem; [exact Hc | lia] ]
  end.

(* A word the block reloads from a byte list (a frame copy of a callee's
   record) is the concatenation of the list's bytes at the reload offset,
   the form the entries and the call facts state words in. *)
Lemma txAccessListReloadedWord (l : list byte) :
  (8 <= length l)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) l)) = listWord64At0 l.
Proof.
  intros Hlen.
  do 8 (destruct l as [|? l]; [cbn in Hlen; lia|]).
  apply bv_eq. rewrite Z_to_bv_unsigned.
  change (N.to_nat 8) with 8%nat. cbn [take List.nth].
  rewrite !concatByteUnsigned by reflexivity.
  rewrite littleEndianBv. cbn [littleEndian take]. clear Hlen.
  change (littleEndian (take 0 l)) with 0.
  repeat match goal with x : byte |- _ =>
    lazymatch goal with
    | _ : 0 <= bv_unsigned x < _ |- _ => fail
    | _ => pose proof (bv_unsigned_in_range _ x)
    end end.
  unfold bv_wrap, bv_modulus in *.
  change (MachineWord.MachineWord.Z_idx 8) with 8%N in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_small by lia. lia.
Qed.

(* The reload offset of such a word is a frame difference that is 0 by
   ring (`sp - 136 - (sp - 424 + 288)`). *)
Ltac txAccessListReloadedWordAt :=
  match goal with
  | |- context [Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop (Z.to_nat ?d) ?l)))] =>
      let Hd := fresh "Hd" in
      assert (Hd : d = 0) by lia;
      rewrite Hd; change (Z.to_nat 0) with 0%nat; rewrite drop_0;
      rewrite (txAccessListReloadedWord l) by lia
  end.
