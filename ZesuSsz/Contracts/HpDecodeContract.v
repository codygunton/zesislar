From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Open Scope Z_scope.

(* W0 held-out entry interface for nibbles.hpDecode (entry 0x80067714).
   Entry interface only: registers, memory footprints, stack frame, ranges and
   a domain, from the calling convention and the caller sites. It states no
   meaning of the result. The source of each fact is in the W0 justification
   table of the held-out run record. *)

Notation hpDecodeStackBytes := ((16) : Z) (only parsing).
Notation hpDecodeResultBytes := ((24) : Z) (only parsing).
Notation hpDecodeStackLow := ((0xa0000000) : Z) (only parsing).
Notation hpDecodeStackHigh := ((0xa0400000) : Z) (only parsing).
Notation hpDecodeReadableLow := ((0x40000000) : Z) (only parsing).
Notation hpDecodeReadableHigh := ((0xc0000000) : Z) (only parsing).

Record HpDecodeArgs : Type := {
  hpDecodeResultPointer : Z;
  hpDecodeBeforeResult : list byte;
  hpDecodeInputPointer : Z;
  hpDecodeInputLength : Z;
  hpDecodeInputBytes : list byte;
  hpDecodeOutputPointer : Z;
  hpDecodeOutputLength : Z;
  hpDecodeBeforeOutput : list byte;
  hpDecodeStackPointer : Z;
  hpDecodeReturnAddress : Z;
  hpDecodeSavedFramePointer : bv 64
}.

Record HpDecodeOutcome : Type := {
  hpDecodeAfterResult : list byte;
  hpDecodeAfterOutput : list byte
}.

Definition hpDecodeSeparate (p n q m : Z) : Prop :=
  p + n <= q \/ q + m <= p.

Definition hpDecodeArgsWellFormed (args : HpDecodeArgs) : Prop :=
  0 <= hpDecodeInputLength args < 2 ^ 64 /\
  Z.of_nat (length (hpDecodeInputBytes args)) = hpDecodeInputLength args /\
  0 <= hpDecodeOutputLength args < 2 ^ 64 /\
  Z.of_nat (length (hpDecodeBeforeOutput args)) = hpDecodeOutputLength args /\
  2 * hpDecodeInputLength args <= hpDecodeOutputLength args /\
  length (hpDecodeBeforeResult args) = 24%nat /\
  hpDecodeReadableLow <= hpDecodeInputPointer args /\
  hpDecodeInputPointer args + hpDecodeInputLength args <= hpDecodeReadableHigh /\
  hpDecodeStackLow <= hpDecodeOutputPointer args /\
  hpDecodeOutputPointer args + hpDecodeOutputLength args <= hpDecodeStackHigh /\
  hpDecodeStackLow <= hpDecodeResultPointer args /\
  hpDecodeResultPointer args + hpDecodeResultBytes <= hpDecodeStackHigh /\
  hpDecodeStackLow + hpDecodeStackBytes <= hpDecodeStackPointer args <= hpDecodeStackHigh /\
  hpDecodeStackPointer args mod 16 = 0 /\
  0 <= hpDecodeReturnAddress args < 2 ^ 64 /\ hpDecodeReturnAddress args mod 4 = 0 /\
  hpDecodeSeparate (hpDecodeInputPointer args) (hpDecodeInputLength args)
    (hpDecodeOutputPointer args) (hpDecodeOutputLength args) /\
  hpDecodeSeparate (hpDecodeInputPointer args) (hpDecodeInputLength args)
    (hpDecodeResultPointer args) hpDecodeResultBytes /\
  hpDecodeSeparate (hpDecodeOutputPointer args) (hpDecodeOutputLength args)
    (hpDecodeResultPointer args) hpDecodeResultBytes /\
  hpDecodeSeparate (hpDecodeInputPointer args) (hpDecodeInputLength args)
    (hpDecodeStackPointer args - hpDecodeStackBytes) hpDecodeStackBytes /\
  hpDecodeSeparate (hpDecodeOutputPointer args) (hpDecodeOutputLength args)
    (hpDecodeStackPointer args - hpDecodeStackBytes) hpDecodeStackBytes /\
  hpDecodeSeparate (hpDecodeResultPointer args) hpDecodeResultBytes
    (hpDecodeStackPointer args - hpDecodeStackBytes) hpDecodeStackBytes.

Definition hpDecodeEntryResources `{!islaG Sigma} `{!threadG}
    (args : HpDecodeArgs) : iProp Sigma :=
  (∃ (x15 x16 x17 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (hpDecodeSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeOutputPointer args)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeOutputLength args)) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   hpDecodeInputPointer args ↦ₘ∗ hpDecodeInputBytes args ∗
   hpDecodeOutputPointer args ↦ₘ∗ hpDecodeBeforeOutput args ∗
   hpDecodeResultPointer args ↦ₘ∗ hpDecodeBeforeResult args ∗
   (hpDecodeStackPointer args - hpDecodeStackBytes) ↦ₘ? hpDecodeStackBytes ∗
   ⌜hpDecodeArgsWellFormed args⌝ ∗ True)%I.

Definition hpDecodeExitRegisterResources `{!islaG Sigma} `{!threadG}
    (args : HpDecodeArgs) : iProp Sigma :=
  (∃ (x11 x12 x13 x14 x15 x16 x17 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (hpDecodeSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (hpDecodeResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   hpDecodeInputPointer args ↦ₘ∗ hpDecodeInputBytes args ∗
   (hpDecodeStackPointer args - hpDecodeStackBytes) ↦ₘ? hpDecodeStackBytes ∗ True)%I.

Definition hpDecodeExitResources `{!islaG Sigma} `{!threadG}
    (args : HpDecodeArgs) (after : HpDecodeOutcome) : iProp Sigma :=
  (hpDecodeOutputPointer args ↦ₘ∗ hpDecodeAfterOutput after ∗
   hpDecodeResultPointer args ↦ₘ∗ hpDecodeAfterResult after ∗
   hpDecodeExitRegisterResources args)%I.

Definition hpDecodeResources `{!islaG Sigma} `{!threadG} (code : iProp Sigma) :
    IslarisContractResources HpDecodeArgs HpDecodeOutcome :=
  {| islarisCode := code;
     islarisEntry := hpDecodeEntryResources;
     islarisExit := hpDecodeExitResources |}.

Definition hpDecodeDomainAt (returnAddress : Z) (args : HpDecodeArgs) : Prop :=
  hpDecodeReturnAddress args = returnAddress /\ hpDecodeArgsWellFormed args.
