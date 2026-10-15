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
Require Import ZesuSsz.Compliance.NextUint64ExitMeanings.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Compliance.NextUint64LoopSteps.

#[export] Instance nextUint64Return62e4MeaningRegistered `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved resultBytes : list byte) :
  ZesuExitMeaning
    (nextUint64EntryAt800d62e4 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      inputBytes sliceBytes decoded saved resultBytes)
  (Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 40%nat saved))) =
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
     length resultBytes = 16%nat) :=
  nextUint64Return62e4Meaning params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    inputBytes sliceBytes decoded saved resultBytes.

#[export] Instance nextUint64Header6318StepRegistered `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args)
    (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) :
  ZesuLoopStep
    (nextUint64EntryAt800d6318 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      inputBytes sliceBytes decoded saved)
  (nextUint64DecodedLength decoded <> 0 /\
    (forall nextByte : byte,
      nth_error (nextUint64Payload (nextUint64Base params) decoded)
        (Z.to_nat (bv_unsigned x12 - nextUint64DecodedPointer decoded)) = Some nextByte ->
      (bv_unsigned x12 + 1 < bv_unsigned x13 ->
       nextUint64FoldInvariant (nextUint64Base params) decoded
         (Z_to_bv 64 (bv_unsigned x12 + 1)) x13
         (Z_to_bv 64 (bv_unsigned x11 * 256 + bv_unsigned nextByte))) /\
      (bv_unsigned x12 + 1 = bv_unsigned x13 ->
       nextUint64FoldComplete (nextUint64Base params) decoded
         (Z_to_bv 64 (bv_unsigned x11 * 256 + bv_unsigned nextByte)))))%Z :=
  nextUint64Header6318Step params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    inputBytes sliceBytes decoded saved.
