From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Open Scope Z_scope.

(* W0 held-out entry interface for modexp.berlinGasCalc (entry 0x800d39a4).
   Entry interface only: registers, stack frame, ranges and a domain, from the
   calling convention and the caller site. It states no meaning of the result.
   The source of each fact is in the W0 justification table of the held-out
   run record. The four exponent-head registers carry the u256 argument as
   64-bit limbs; the interface gives them no meaning. *)

Notation berlinGasCalcStackBytes := ((64) : Z) (only parsing).
Notation berlinGasCalcStackLow := ((0xa0000000) : Z) (only parsing).
Notation berlinGasCalcStackHigh := ((0xa0400000) : Z) (only parsing).

Record BerlinGasCalcArgs : Type := {
  berlinBaseLength : bv 64;
  berlinExponentLength : bv 64;
  berlinModulusLength : bv 64;
  berlinExponentHead0 : bv 64;
  berlinExponentHead1 : bv 64;
  berlinExponentHead2 : bv 64;
  berlinExponentHead3 : bv 64;
  berlinStackPointer : Z;
  berlinReturnAddress : Z;
  berlinSavedFramePointer : bv 64
}.

Record BerlinGasCalcOutcome : Type := {
  berlinGas : bv 64
}.

Definition berlinGasCalcArgsWellFormed (args : BerlinGasCalcArgs) : Prop :=
  berlinGasCalcStackLow + berlinGasCalcStackBytes <= berlinStackPointer args <= berlinGasCalcStackHigh /\
  berlinStackPointer args mod 16 = 0 /\
  0 <= berlinReturnAddress args < 2 ^ 64 /\ berlinReturnAddress args mod 4 = 0.

Definition berlinGasCalcEntryResources `{!islaG Sigma} `{!threadG}
    (args : BerlinGasCalcArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x17 x28 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (berlinReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (berlinStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (berlinSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (berlinBaseLength args) ∗
   "x11" ↦ᵣ RVal_Bits (berlinExponentLength args) ∗
   "x12" ↦ᵣ RVal_Bits (berlinModulusLength args) ∗
   "x13" ↦ᵣ RVal_Bits (berlinExponentHead0 args) ∗
   "x14" ↦ᵣ RVal_Bits (berlinExponentHead1 args) ∗
   "x15" ↦ᵣ RVal_Bits (berlinExponentHead2 args) ∗
   "x16" ↦ᵣ RVal_Bits (berlinExponentHead3 args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x17" ↦ᵣ RVal_Bits x17 ∗ "x28" ↦ᵣ RVal_Bits x28 ∗
   (berlinStackPointer args - berlinGasCalcStackBytes) ↦ₘ? berlinGasCalcStackBytes ∗
   ⌜berlinGasCalcArgsWellFormed args⌝ ∗ True)%I.

Definition berlinGasCalcExitResources `{!islaG Sigma} `{!threadG}
    (args : BerlinGasCalcArgs) (after : BerlinGasCalcOutcome) : iProp Sigma :=
  (∃ (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (berlinReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (berlinStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (berlinSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (berlinGas after) ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x17" ↦ᵣ RVal_Bits x17 ∗ "x28" ↦ᵣ RVal_Bits x28 ∗
   (berlinStackPointer args - berlinGasCalcStackBytes) ↦ₘ? berlinGasCalcStackBytes ∗
   True)%I.

Definition berlinGasCalcResources `{!islaG Sigma} `{!threadG} (code : iProp Sigma) :
    IslarisContractResources BerlinGasCalcArgs BerlinGasCalcOutcome :=
  {| islarisCode := code;
     islarisEntry := berlinGasCalcEntryResources;
     islarisExit := berlinGasCalcExitResources |}.

Definition berlinGasCalcDomainAt (returnAddress : Z) (args : BerlinGasCalcArgs) : Prop :=
  berlinReturnAddress args = returnAddress /\ berlinGasCalcArgsWellFormed args.
