Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.SwitchScopeCarrier.

Lemma switch_scope_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuSsz.Automation.PureFacts.ZesuRuleSetV2) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.InteriorByteSlice.ZesuStepInteriorByteSlice) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepArrayBounds) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ArrayLoadPriority.ZesuStepArrayLoadPriority) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.BoundedArithmetic.ZesuStepBoundedArithmetic) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ByteFold.ZesuStepByteFold) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.CallReturn.ZesuStepCallReturn) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.CallReturnSpecTable.ZesuStepCallReturnSpecTable) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ExistentialArrayRestore.ZesuStepExistentialArrayRestore) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.InstrPreAddress.ZesuStepInstrPreAddress) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepInstructionLookup) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.LoadedTrace.ZesuStepLoadedTrace) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.LookupReduce.ZesuStepLookupReduce) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.BitvectorFacts.ZesuStepLowMask) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.OutcomeHandoff.ZesuStepOutcomeHandoff) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRamFault) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRecordWitness) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ReturnBundle.ZesuStepReturnBundle) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ReturnWand.ZesuStepReturnWand) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.SealedCoverage.ZesuStepSealedOpen) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.SpecPrefix.ZesuStepSpecTail) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepStackWrite) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.TracePrefixTail.ZesuStepTracePrefixTail) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.PureFacts.ZesuStepWitnessArith) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ByteArrays.ZesuStepWordArrayHandoff) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ArrayLoadPriority.ZesuStepWordArrayLookup) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.ArrayBounds.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Require Import ZesuSsz.Automation.Switches.ByteFold.
Require Import ZesuSsz.Automation.Switches.CallReturn.
Require Import ZesuSsz.Automation.Switches.CallReturnSpecTable.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Require Import ZesuSsz.Automation.Switches.ExistentialArrayRestore.
Require Import ZesuSsz.Automation.Switches.InstrPreAddress.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.IntegerArrayAddress.
Require Import ZesuSsz.Automation.Switches.InteriorByteSlice.
Require Import ZesuSsz.Automation.Switches.LoadedTrace.
Require Import ZesuSsz.Automation.Switches.LookupReduce.
Require Import ZesuSsz.Automation.Switches.LowMask.
Require Import ZesuSsz.Automation.Switches.OutcomeHandoff.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ReturnWand.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
Require Import ZesuSsz.Automation.Switches.SpecTail.
Require Import ZesuSsz.Automation.Switches.StackWrite.
Require Import ZesuSsz.Automation.Switches.TracePrefixTail.
Require Import ZesuSsz.Automation.Switches.WitnessArith.
Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.
Require Import ZesuSsz.Automation.Switches.WordArrayLookup.

Lemma switch_scope_direct_activation : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation.PureFacts.ZesuRuleSetV2) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.InteriorByteSlice.ZesuStepInteriorByteSlice) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepArrayBounds) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ArrayLoadPriority.ZesuStepArrayLoadPriority) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.BoundedArithmetic.ZesuStepBoundedArithmetic) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ByteFold.ZesuStepByteFold) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.CallReturn.ZesuStepCallReturn) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.CallReturnSpecTable.ZesuStepCallReturnSpecTable) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ExistentialArrayRestore.ZesuStepExistentialArrayRestore) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.InstrPreAddress.ZesuStepInstrPreAddress) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepInstructionLookup) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.LoadedTrace.ZesuStepLoadedTrace) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.LookupReduce.ZesuStepLookupReduce) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.BitvectorFacts.ZesuStepLowMask) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.OutcomeHandoff.ZesuStepOutcomeHandoff) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRamFault) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRecordWitness) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ReturnBundle.ZesuStepReturnBundle) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ReturnWand.ZesuStepReturnWand) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.SealedCoverage.ZesuStepSealedOpen) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.SpecPrefix.ZesuStepSpecTail) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepStackWrite) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.TracePrefixTail.ZesuStepTracePrefixTail) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.PureFacts.ZesuStepWitnessArith) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ByteArrays.ZesuStepWordArrayHandoff) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation.ArrayLoadPriority.ZesuStepWordArrayLookup) in idtac.
  exact I.
Qed.

Print Assumptions switch_scope_direct_activation.
