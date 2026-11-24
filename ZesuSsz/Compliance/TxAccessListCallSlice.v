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
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.TxAccessListContract.
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
