From Coq Require Import ZArith.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import Scaffolding.DecodeItemComplianceStatement.
Require Import Scaffolding.DecodeItemSignatureGates.

Definition fixtureExtraPremise : Prop :=
  False -> DecodeItemComplianceStatement.
Fail Check (eq_refl : fixtureExtraPremise = ReviewedDecodeItemComplianceType).

Definition fixtureMissingRamStackBound (inputPointer inputLength resultPointer
    stackPointer returnAddress inputEnd : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 40 < word64Modulus /\
  decodeItemStackBytes <= stackPointer < word64Modulus /\
  separateRanges inputPointer inputLength resultPointer 40 /\
  separateRanges inputPointer inputLength
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  separateRanges resultPointer 40
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0 /\
  ((mapInputBufferAddress defaultMap <= inputPointer /\
    inputPointer + inputLength <=
      mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= inputPointer /\
    inputPointer + inputLength <= machineRamEnd defaultMap)) /\
  mapRamBase defaultMap <= resultPointer /\
  resultPointer + 40 <= machineRamEnd defaultMap /\
  0 <= inputEnd < word64Modulus /\
  inputPointer + inputLength <= inputEnd.
Fail Check (eq_refl : fixtureMissingRamStackBound =
                 ReviewedDecodeItemEntryLayout).

Definition fixtureMissingReadableInputBound (inputPointer inputLength resultPointer
    stackPointer returnAddress inputEnd : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 40 < word64Modulus /\
  decodeItemStackBytes <= stackPointer < word64Modulus /\
  mapRamBase defaultMap + decodeItemStackBytes <= stackPointer /\
  stackPointer <= machineRamEnd defaultMap /\
  separateRanges inputPointer inputLength resultPointer 40 /\
  separateRanges inputPointer inputLength
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  separateRanges resultPointer 40
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0 /\
  mapRamBase defaultMap <= resultPointer /\
  resultPointer + 40 <= machineRamEnd defaultMap /\
  0 <= inputEnd < word64Modulus /\
  inputPointer + inputLength <= inputEnd.
Fail Check (eq_refl : fixtureMissingReadableInputBound = ReviewedDecodeItemEntryLayout).

Definition fixtureMissingRamOutputBound (inputPointer inputLength resultPointer
    stackPointer returnAddress inputEnd : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 40 < word64Modulus /\
  decodeItemStackBytes <= stackPointer < word64Modulus /\
  mapRamBase defaultMap + decodeItemStackBytes <= stackPointer /\
  stackPointer <= machineRamEnd defaultMap /\
  separateRanges inputPointer inputLength resultPointer 40 /\
  separateRanges inputPointer inputLength
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  separateRanges resultPointer 40
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0 /\
  ((mapInputBufferAddress defaultMap <= inputPointer /\
    inputPointer + inputLength <=
      mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= inputPointer /\
    inputPointer + inputLength <= machineRamEnd defaultMap)) /\
  0 <= inputEnd < word64Modulus /\
  inputPointer + inputLength <= inputEnd.
Fail Check (eq_refl : fixtureMissingRamOutputBound = ReviewedDecodeItemEntryLayout).

Definition fixtureMissingInputEndBound (inputPointer inputLength resultPointer
    stackPointer returnAddress inputEnd : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 40 < word64Modulus /\
  decodeItemStackBytes <= stackPointer < word64Modulus /\
  mapRamBase defaultMap + decodeItemStackBytes <= stackPointer /\
  stackPointer <= machineRamEnd defaultMap /\
  separateRanges inputPointer inputLength resultPointer 40 /\
  separateRanges inputPointer inputLength
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  separateRanges resultPointer 40
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0 /\
  ((mapInputBufferAddress defaultMap <= inputPointer /\
    inputPointer + inputLength <=
      mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= inputPointer /\
    inputPointer + inputLength <= machineRamEnd defaultMap)) /\
  mapRamBase defaultMap <= resultPointer /\
  resultPointer + 40 <= machineRamEnd defaultMap.
Fail Check (eq_refl : fixtureMissingInputEndBound = ReviewedDecodeItemEntryLayout).

Definition fixtureUnboundedInputSysRegs (_ : DecodeItemArgs) :=
  InstrSpecs.Machine.zesu_sys_regs.
Fail Check (eq_refl : fixtureUnboundedInputSysRegs = decodeItemSysRegs).

Definition fixtureChangedDomainModel (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  let model := decodeItemSelectedModel returnAddress in
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress (fun _ => True) args /\
       DecodeMeaningModuloKnownBugs args after;
     islarisContractStep := islarisContractStep _ _ model;
     islarisContractResources := islarisContractResources _ _ model |}.

Definition fixtureChangedDomain : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (fixtureChangedDomainModel returnAddress).
Fail Check (eq_refl : fixtureChangedDomain = ReviewedDecodeItemComplianceType).

Definition fixtureEvaluatorModel
    (evaluator : DecodeItemArgs -> DecodeItemOutcome -> Prop)
    (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  let model := decodeItemSelectedModel returnAddress in
  {| islarisContractAllows := evaluator;
     islarisContractStep := islarisContractStep _ _ model;
     islarisContractResources := islarisContractResources _ _ model |}.

Definition fixtureHiddenEvaluator
    (evaluator : DecodeItemArgs -> DecodeItemOutcome -> Prop) : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (fixtureEvaluatorModel evaluator returnAddress).
Fail Check (@fixtureHiddenEvaluator : ReviewedDecodeItemComplianceType).

Require Import Scaffolding.DecodeItemSemanticEntryFixtures.
