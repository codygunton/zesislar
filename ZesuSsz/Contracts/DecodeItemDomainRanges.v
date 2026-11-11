Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.

#[export] Instance decodeItemDomainAtInputPointerRangeDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    (0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputPointer args <
      stdpp.bitvector.definitions.bv_modulus 64%N)%Z.
Proof.
  unfold ZesuSsz.Automation.PureFacts.ZesuDerivedFacts,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout.
  intros [_ [_ [_ [Hlow [Hnonnegative [Hupper Hrest]]]]]].
  split; [exact Hlow |].
  change (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputPointer args <
    ZesuSsz.Contracts.RlpDecodeItem.word64Modulus)%Z.
  pose proof (proj1 (Z.add_le_mono_l 0 _ (decodeItemInputPointer args))
    Hnonnegative) as Hstep.
  rewrite Z.add_0_r in Hstep.
  exact (Z.le_lt_trans _ _ _ Hstep Hupper).
Qed.
Print Assumptions decodeItemDomainAtInputPointerRangeDerivedFacts.

#[export] Instance decodeItemDomainAtInputLengthRangeDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    (0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength args <
      stdpp.bitvector.definitions.bv_modulus 64%N)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  destruct Hdomain as [_ [_ [_ [Hlow [Hnonnegative [Hupper Hrest]]]]]].
  change (0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength args <
    ZesuSsz.Contracts.RlpDecodeItem.word64Modulus)%Z.
  split; [exact Hnonnegative |].
  pose proof (proj1 (Z.add_le_mono_r 0 _ (decodeItemInputLength args))
    Hlow) as Hstep.
  rewrite Z.add_0_l in Hstep.
  exact (Z.le_lt_trans _ _ _ Hstep Hupper).
Qed.
Print Assumptions decodeItemDomainAtInputLengthRangeDerivedFacts.

(* The function-entry statement's return-address conjunct: the Level-1
   layout keeps returnAddress in range and 4-aligned. *)
Lemma decodeItemDomainAtReturnAlignment (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args)) mod 4 = 0)%Z.
Proof.
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed, decodeItemEntryLayout.
  intros domain. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  assumption.
Qed.
