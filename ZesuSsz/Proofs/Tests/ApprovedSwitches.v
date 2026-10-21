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
  ZesuSsz.Automation.IntegerReturn.ZesuStepIntegerReturn /\
  ZesuSsz.Automation.ExitMeaning.ZesuStepExitMeaning /\
  ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch.
Proof.
  repeat apply conj.
  all: typeclasses eauto.
Qed.

Print Assumptions approved_switch_inventory.

Lemma approved_switch_dispatch_caches_normalizers : True.
Proof.
  let switches := ZesuSsz.Automation.Finish.zesu_search_switches in
  ZesuSsz.Automation.SwitchDispatch.zesu_with_switches switches ltac:(fun _ =>
    let rec require_enabled wanted entries :=
      lazymatch entries with
      | cons (?candidate, ?enabled) ?rest =>
          tryif constr_eq wanted candidate
          then constr_eq enabled true
          else require_enabled wanted rest
      end in
    lazymatch goal with
    | _ : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache ?entries |- _ =>
        require_enabled constr:(ZesuSsz.Automation.BitvectorFacts.ZesuStepMaskNormalizer) entries;
        require_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepPureFactExistential) entries;
        require_enabled constr:(ZesuSsz.Automation.IntegerReturn.ZesuStepIntegerReturn) entries;
        require_enabled constr:(ZesuSsz.Automation.ExitMeaning.ZesuStepExitMeaning) entries;
        require_enabled constr:(ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch) entries
    end;
    exact I).
Qed.

Print Assumptions approved_switch_dispatch_caches_normalizers.
