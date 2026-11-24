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
