(* Measurement only: every searched switch that `All.v` leaves off.
   Not for merge. *)
Require ZesuSsz.Automation2.ContextCollection ZesuSsz.Automation2.Hooks
  ZesuSsz.Automation2.BitvectorFacts ZesuSsz.Automation2.EntryIntro
  ZesuSsz.Automation2.ByteArrays ZesuSsz.Automation2.ReturnBundle
  ZesuSsz.Automation2.ReturnWand ZesuSsz.Automation2.IntegerReturn
  ZesuSsz.Automation2.ExitMeaning ZesuSsz.Automation2.ConjunctMatch
  ZesuSsz.Automation2.Finish.
#[export] Instance zesu_switch_experiment_0 : ZesuSsz.Automation2.ContextCollection.ZesuStepContextCollection := ltac:(constructor).
#[export] Instance zesu_switch_experiment_1 : ZesuSsz.Automation2.Hooks.ZesuStepRegionFaultNormalization := ltac:(constructor).
#[export] Instance zesu_switch_experiment_2 : ZesuSsz.Automation2.Hooks.ZesuStepInstructionLookup := ltac:(constructor).
#[export] Instance zesu_switch_experiment_3 : ZesuSsz.Automation2.Hooks.ZesuStepStackWrite := ltac:(constructor).
#[export] Instance zesu_switch_experiment_4 : ZesuSsz.Automation2.Hooks.ZesuStepRamFault := ltac:(constructor).
#[export] Instance zesu_switch_experiment_5 : ZesuSsz.Automation2.Hooks.ZesuStepRegionFault := ltac:(constructor).
#[export] Instance zesu_switch_experiment_6 : ZesuSsz.Automation2.BitvectorFacts.ZesuStepLowMask := ltac:(constructor).
#[export] Instance zesu_switch_experiment_7 : ZesuSsz.Automation2.EntryIntro.ZesuStepEntryIntro := ltac:(constructor).
#[export] Instance zesu_switch_experiment_8 : ZesuSsz.Automation2.Hooks.ZesuStepRecordWitness := ltac:(constructor).
#[export] Instance zesu_switch_experiment_9 : ZesuSsz.Automation2.ByteArrays.ZesuStepWordArrayHandoff := ltac:(constructor).
#[export] Instance zesu_switch_experiment_10 : ZesuSsz.Automation2.ReturnBundle.ZesuStepReturnBundle := ltac:(constructor).
#[export] Instance zesu_switch_experiment_11 : ZesuSsz.Automation2.ReturnWand.ZesuStepReturnWand := ltac:(constructor).
#[export] Instance zesu_switch_experiment_12 : ZesuSsz.Automation2.BitvectorFacts.ZesuStepStrictSigned := ltac:(constructor).
#[export] Instance zesu_switch_experiment_13 : ZesuSsz.Automation2.Hooks.ZesuStepListWitness := ltac:(constructor).
#[export] Instance zesu_switch_experiment_14 : ZesuSsz.Automation2.Hooks.ZesuStepTupleWitness := ltac:(constructor).
#[export] Instance zesu_switch_experiment_15 : ZesuSsz.Automation2.Hooks.ZesuStepKnownPairWitness := ltac:(constructor).
#[export] Instance zesu_switch_experiment_16 : ZesuSsz.Automation2.Hooks.ZesuStepPureWitnessConstraints := ltac:(constructor).
#[export] Instance zesu_switch_experiment_17 : ZesuSsz.Automation2.Hooks.ZesuStepEvarSideconditionGuard := ltac:(constructor).
#[export] Instance zesu_switch_experiment_18 : ZesuSsz.Automation2.Hooks.ZesuStepEvarImplicationGuard := ltac:(constructor).
#[export] Instance zesu_switch_experiment_19 : ZesuSsz.Automation2.Hooks.ZesuStepCanonicalAnchor := ltac:(constructor).
#[export] Instance zesu_switch_experiment_20 : ZesuSsz.Automation2.Hooks.ZesuStepCanonicalPureConjunction := ltac:(constructor).
#[export] Instance zesu_switch_experiment_21 : ZesuSsz.Automation2.Hooks.ZesuStepByteListContainment := ltac:(constructor).
#[export] Instance zesu_switch_experiment_22 : ZesuSsz.Automation2.Hooks.ZesuStepRegionFaultCastHypotheses := ltac:(constructor).
#[export] Instance zesu_switch_experiment_23 : ZesuSsz.Automation2.Hooks.ZesuStepPureFactExistential := ltac:(constructor).
#[export] Instance zesu_switch_experiment_24 : ZesuSsz.Automation2.IntegerReturn.ZesuStepIntegerReturn := ltac:(constructor).
#[export] Instance zesu_switch_experiment_25 : ZesuSsz.Automation2.ExitMeaning.ZesuStepExitMeaning := ltac:(constructor).
#[export] Instance zesu_switch_experiment_26 : ZesuSsz.Automation2.ConjunctMatch.ZesuStepConjunctMatch := ltac:(constructor).
