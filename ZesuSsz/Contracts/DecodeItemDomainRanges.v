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

#[export] Instance decodeItemDomainAtOutputPointerBoundsDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    ((0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args < ZesuSsz.Contracts.RlpDecodeItem.word64Modulus) /\
  ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args + 40 < ZesuSsz.Contracts.RlpDecodeItem.word64Modulus /\
  ZesuMachineMap.Machine.mapRamBase ZesuMachineMap.Machine.defaultMap <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args /\
  ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args + 40 <= ZesuMachineMap.Machine.machineRamEnd ZesuMachineMap.Machine.defaultMap)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  repeat split; first [assumption | lia].
Qed.
Print Assumptions decodeItemDomainAtOutputPointerBoundsDerivedFacts.

#[export] Instance decodeItemDomainAtStackRamBoundsDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    (ZesuMachineMap.Machine.mapRamBase ZesuMachineMap.Machine.defaultMap + ZesuSsz.Contracts.RlpDecodeItem.decodeItemStackBytes <=
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemStackPointer args /\
  ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemStackPointer args <= ZesuMachineMap.Machine.machineRamEnd ZesuMachineMap.Machine.defaultMap)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  repeat split; first [assumption | lia].
Qed.
Print Assumptions decodeItemDomainAtStackRamBoundsDerivedFacts.

#[export] Instance decodeItemDomainAtReturnAddressBoundsDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    ((0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemReturnAddress args < ZesuSsz.Contracts.RlpDecodeItem.word64Modulus) /\
  ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemReturnAddress args mod 4 = 0)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  repeat split; first [assumption | lia].
Qed.
Print Assumptions decodeItemDomainAtReturnAddressBoundsDerivedFacts.

#[export] Instance decodeItemDomainAtSeparateRangesDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    (ZesuSsz.Contracts.RlpDecodeItem.separateRanges (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputPointer args)
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength args) (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args) 40 /\
  ZesuSsz.Contracts.RlpDecodeItem.separateRanges (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputPointer args)
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength args)
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemStackPointer args - ZesuSsz.Contracts.RlpDecodeItem.decodeItemStackBytes)
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemStackBytes /\
  ZesuSsz.Contracts.RlpDecodeItem.separateRanges (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemOutputPointer args) 40
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemStackPointer args - ZesuSsz.Contracts.RlpDecodeItem.decodeItemStackBytes)
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemStackBytes)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  repeat split; first [assumption | lia].
Qed.
Print Assumptions decodeItemDomainAtSeparateRangesDerivedFacts.

#[export] Instance decodeItemDomainAtStorageLengthDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z)
    (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    ((List.length (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemBeforeStorage args) = 40)%nat)%Z.
Proof.
  intro Hdomain.
  unfold ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain,
    ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemArgsWellFormed,
    ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  repeat split; first [assumption | lia].
Qed.
Print Assumptions decodeItemDomainAtStorageLengthDerivedFacts.
