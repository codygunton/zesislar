From Coq Require Import ZArith.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import Scaffolding.DecodeItemComplianceStatement.

Definition ReviewedDecodeItemEntryLayout (inputPointer inputLength resultPointer
    stackPointer returnAddress : Z) : Prop :=
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

Check (eq_refl : decodeItemEntryLayout = ReviewedDecodeItemEntryLayout).

(* Pending gate: no implementation theorem exists for this statement yet. *)
Definition ReviewedDecodeItemComplianceType : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).

Check (@DecodeItemComplianceStatement : Prop).
Check (eq_refl : DecodeItemComplianceStatement =
                 ReviewedDecodeItemComplianceType).
Check (eq_refl : ReviewedDecodeItemComplianceType =
                 DecodeItemSelectedComplianceStatement).
