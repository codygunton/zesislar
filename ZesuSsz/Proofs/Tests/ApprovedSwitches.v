Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.

Lemma approved_switch_inventory :
  ZesuSsz.Automation.Hooks.ZesuStepInstructionLookup /\
  ZesuSsz.Automation.Hooks.ZesuStepStackWrite /\
  ZesuSsz.Automation.Hooks.ZesuStepRamFault /\
  ZesuSsz.Automation.Hooks.ZesuStepRegionFault /\
  ZesuSsz.Automation.BitvectorFacts.ZesuStepLowMask /\
  ZesuSsz.Automation.BitvectorFacts.ZesuStepMaskNormalizer /\
  ZesuSsz.Automation.EntryIntro.ZesuStepEntryIntro /\
  ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress /\
  ZesuSsz.Automation.Hooks.ZesuStepRecordWitness /\
  ZesuSsz.Automation.Hooks.ZesuStepArrayBounds /\
  ZesuSsz.Automation.ByteArrays.ZesuStepWordArrayHandoff /\
  ZesuSsz.Automation.ReturnBundle.ZesuStepReturnBundle /\
  ZesuSsz.Automation.ReturnWand.ZesuStepReturnWand /\
  ZesuSsz.Automation.BitvectorFacts.ZesuStepStrictSigned /\
  ZesuSsz.Automation.Hooks.ZesuStepListWitness /\
  ZesuSsz.Automation.Hooks.ZesuStepTupleWitness /\
  ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds /\
  ZesuSsz.Automation.Hooks.ZesuStepPureFactHints /\
  ZesuSsz.Automation.Hooks.ZesuStepKnownPairWitness /\
  ZesuSsz.Automation.Hooks.ZesuStepPureWitnessConstraints /\
  ZesuSsz.Automation.Hooks.ZesuStepRegisterCollectionSelection /\
  ZesuSsz.Automation.Hooks.ZesuStepEvarSideconditionGuard /\
  ZesuSsz.Automation.Hooks.ZesuStepRegionFaultNormalization /\
  ZesuSsz.Automation.Hooks.ZesuStepCanonicalAnchor /\
  ZesuSsz.Automation.Hooks.ZesuStepEvarImplicationGuard /\
  ZesuSsz.Automation.SwitchDispatch.ZesuStepSwitchDispatch /\
  ZesuSsz.Automation.Hooks.ZesuStepPureFactExistential /\
  ZesuSsz.Automation.Hooks.ZesuStepCanonicalPureConjunction /\
  ZesuSsz.Automation.Hooks.ZesuStepByteListContainment /\
  ZesuSsz.Automation.Hooks.ZesuStepRegionFaultCastHypotheses /\
  ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch.
Proof.
  Fail assert (Hdisabled : ZesuSsz.Automation.ReturnRoute.ZesuStepReturnRoute)
    by typeclasses eauto.
  repeat apply conj.
  all: typeclasses eauto.
Qed.

Print Assumptions approved_switch_inventory.
