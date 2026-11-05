Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import ZArith.ZArith Lia.

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
  lia.
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
  lia.
Qed.
Print Assumptions decodeItemDomainAtInputLengthRangeDerivedFacts.
