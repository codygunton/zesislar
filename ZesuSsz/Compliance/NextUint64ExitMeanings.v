Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Contract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.

Lemma nextUint64Word64AtDecoder (bytes : list byte) (offset : nat) (value : Z) :
  word64At bytes offset value ->
  Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop offset bytes))) =
    Z_to_bv 64%N value.
Proof.
  intros [_ Hvalue]. f_equal.
  rewrite <- decodeItemByteDecoderBridge. exact Hvalue.
Qed.

Lemma nextUint64SavedReturnDecoder (args : NextUint64Call) (saved : list byte) :
  nextUint64SavedFrameFacts args saved ->
  Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 40%nat saved))) =
    Z_to_bv 64%N (nextReturnAddress args).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hreturn).
  apply nextUint64Word64AtDecoder. exact Hreturn.
Qed.

Lemma nextUint64SavedFrameDecoder (args : NextUint64Call) (saved : list byte) :
  nextUint64SavedFrameFacts args saved ->
  Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 32%nat saved))) =
    nextSavedS0 args.
Proof.
  intros (_ & _ & _ & _ & _ & Hframe & _).
  pose proof (nextUint64Word64AtDecoder saved 32 (bv_unsigned (nextSavedS0 args))
    Hframe) as Hdecoded.
  rewrite Z_to_bv_bv_unsigned in Hdecoded. exact Hdecoded.
Qed.

Lemma nextUint64Return62e4Meaning `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved resultBytes : list byte) :
  nextUint64EntryAt800d62e4 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      inputBytes sliceBytes decoded saved resultBytes ⊢
  ⌜  (Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 40%nat saved))) =
     Z_to_bv 64%N (nextReturnAddress (nextUint64Base params)) /\
   Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 32%nat saved))) =
     nextSavedS0 (nextUint64Base params) /\
   0 <= nextReturnAddress (nextUint64Base params) < word64Modulus /\
   nextReturnAddress (nextUint64Base params) mod 4 = 0 /\
   bv_add (Z_to_bv 64%N (nextStackPointer (nextUint64Base params) - 96))
     (Z_to_bv 64%N 96) = Z_to_bv 64%N (nextStackPointer (nextUint64Base params)) /\
   nextUint64BoundaryDomain params /\
   exists result : NextUint64Return,
     nextResultBytes result = resultBytes /\
     sliceBytes = nextUint64SliceImage (nextRestPointer result) (nextRestLength result) /\
     nextUint64RootResult (nextUint64Base params) result /\
     length resultBytes = 16%nat)⌝.

Proof.
  unfold nextUint64EntryAt800d62e4.
  iIntros "(_ & _ & _ & _ & %Hfacts & _)". iPureIntro.
  destruct Hfacts as [Hpost [result [Hbytes [Hmeaning [Hslice [Hlength Hcursor]]]]]].
  unfold nextUint64PostFacts in Hpost.
  destruct Hpost as (Hdomain & Hinput & Hdecoded & Hsaved & Hregisters).
  pose proof (nextUint64SavedReturnDecoder (nextUint64Base params) saved Hsaved) as Hreturn.
  pose proof (nextUint64SavedFrameDecoder (nextUint64Base params) saved Hsaved) as Hframe.
  pose proof (proj1 Hdomain) as Hlayout. unfold nextUint64EntryLayout in Hlayout.
  assert (Hrange : 0 <= nextReturnAddress (nextUint64Base params) < word64Modulus) by tauto.
  assert (Haligned : nextReturnAddress (nextUint64Base params) mod 4 = 0) by tauto.
  split; [exact Hreturn |]. split; [exact Hframe |].
  split; [exact Hrange |]. split; [exact Haligned |].
  split; [bv_solve |]. split; [exact Hdomain |].
  exists result. split; [exact Hbytes |]. split; [exact Hslice |].
  split; [exact Hmeaning | exact Hlength].
Qed.
