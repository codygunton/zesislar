From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Open Scope Z_scope.

(* Measurement-only entry interface for rlp_decode.decodeParentHeader
   (entry 0x800d5cb8), in the W0 entry-interface shape that the generator
   reads. It is NOT the Level 1 contract: ParentHeaderSelected.v keeps that
   role until the user rules on the contract changes listed in
   _build/agents/parent-header/REPORT.md. It states registers, memory
   footprints, frames, ranges and a domain, and no meaning of the result.
   Differences from parentHeaderSelectedEntry: all general registers are
   owned (temporaries as witnesses, x25-x27 saved); zisk_input_end is fixed
   to the input end that decodeItem's domain needs; the frame is
   uninitialized; the 112 bytes below the frame hold the callee frames
   (decodeItem 16, nextUint64 96 + 16); the stack pointer is 16-aligned and
   in RAM; the input lies in the input buffer. The memcpy tail resources
   (rodata error union, extra-params scratch) are absent. *)

Notation parentHeaderFrameBytes := ((400) : Z) (only parsing).
Notation parentHeaderCalleeBytes := ((112) : Z) (only parsing).
Notation parentHeaderResultSize := ((80) : Z) (only parsing).
Notation parentHeaderRamLow := ((0xa0000000) : Z) (only parsing).
Notation parentHeaderRamHigh := ((0xc0000000) : Z) (only parsing).
Notation parentHeaderInputLow := ((0x40000000) : Z) (only parsing).
Notation parentHeaderInputHigh := ((0x80000000) : Z) (only parsing).

Record ParentHeaderArgs : Type := {
  parentHeaderResultPointer : Z;
  parentHeaderInputPointer : Z;
  parentHeaderInputLength : Z;
  parentHeaderInputBytes : list byte;
  parentHeaderInputEnd : Z;
  parentHeaderStackPointer : Z;
  parentHeaderReturnAddress : Z;
  parentHeaderSavedX8 : bv 64; parentHeaderSavedX9 : bv 64;
  parentHeaderSavedX18 : bv 64; parentHeaderSavedX19 : bv 64;
  parentHeaderSavedX20 : bv 64; parentHeaderSavedX21 : bv 64;
  parentHeaderSavedX22 : bv 64; parentHeaderSavedX23 : bv 64;
  parentHeaderSavedX24 : bv 64; parentHeaderSavedX25 : bv 64;
  parentHeaderSavedX26 : bv 64; parentHeaderSavedX27 : bv 64
}.

Record ParentHeaderOutcome : Type := {
  parentHeaderAfterResult : list byte
}.

Definition parentHeaderSeparate (p n q m : Z) : Prop :=
  p + n <= q \/ q + m <= p.

Definition parentHeaderArgsWellFormed (args : ParentHeaderArgs) : Prop :=
  0 <= parentHeaderInputLength args < 2 ^ 64 /\
  Z.of_nat (length (parentHeaderInputBytes args)) = parentHeaderInputLength args /\
  parentHeaderInputLow <= parentHeaderInputPointer args /\
  parentHeaderInputPointer args + parentHeaderInputLength args <= parentHeaderInputHigh /\
  parentHeaderInputPointer args + parentHeaderInputLength args <= parentHeaderInputEnd args /\
  parentHeaderInputEnd args < 2 ^ 64 /\
  parentHeaderRamLow <= parentHeaderResultPointer args /\
  parentHeaderResultPointer args + parentHeaderResultSize <= parentHeaderRamHigh /\
  parentHeaderRamLow + parentHeaderFrameBytes + parentHeaderCalleeBytes <= parentHeaderStackPointer args /\
  parentHeaderStackPointer args < parentHeaderRamHigh /\
  parentHeaderStackPointer args mod 16 = 0 /\
  0 <= parentHeaderReturnAddress args < 2 ^ 64 /\ parentHeaderReturnAddress args mod 4 = 0 /\
  parentHeaderSeparate (parentHeaderInputPointer args) (parentHeaderInputLength args)
    (parentHeaderResultPointer args) parentHeaderResultSize /\
  parentHeaderSeparate (parentHeaderInputPointer args) (parentHeaderInputLength args)
    (parentHeaderStackPointer args - parentHeaderFrameBytes) parentHeaderFrameBytes /\
  parentHeaderSeparate (parentHeaderInputPointer args) (parentHeaderInputLength args)
    (parentHeaderStackPointer args - parentHeaderFrameBytes - parentHeaderCalleeBytes) parentHeaderCalleeBytes /\
  parentHeaderSeparate (parentHeaderResultPointer args) parentHeaderResultSize
    (parentHeaderStackPointer args - parentHeaderFrameBytes) parentHeaderFrameBytes /\
  parentHeaderSeparate (parentHeaderResultPointer args) parentHeaderResultSize
    (parentHeaderStackPointer args - parentHeaderFrameBytes - parentHeaderCalleeBytes) parentHeaderCalleeBytes.

(* zisk_input_end holds the input end, as decodeItemSysRegs states for decodeItem. *)
Definition parentHeaderSysRegs (args : ParentHeaderArgs) : list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (Z_to_bv 64 (parentHeaderInputEnd args)))
        else shape)) zesu_sys_regs.

Definition parentHeaderEntryResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (parentHeaderSysRegs args) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderStackPointer args)) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (parentHeaderSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (parentHeaderSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (parentHeaderSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (parentHeaderSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (parentHeaderSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (parentHeaderSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (parentHeaderSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (parentHeaderSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (parentHeaderSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (parentHeaderSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (parentHeaderSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (parentHeaderSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   parentHeaderInputPointer args ↦ₘ∗ parentHeaderInputBytes args ∗
   parentHeaderResultPointer args ↦ₘ? parentHeaderResultSize ∗
   (parentHeaderStackPointer args - parentHeaderFrameBytes) ↦ₘ? parentHeaderFrameBytes ∗
   (parentHeaderStackPointer args - parentHeaderFrameBytes - parentHeaderCalleeBytes) ↦ₘ?
     parentHeaderCalleeBytes ∗
   ⌜parentHeaderArgsWellFormed args⌝ ∗ True)%I.

Definition parentHeaderExitRegisterResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (parentHeaderSysRegs args) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (parentHeaderStackPointer args)) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (parentHeaderSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (parentHeaderSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (parentHeaderSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (parentHeaderSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (parentHeaderSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (parentHeaderSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (parentHeaderSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (parentHeaderSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (parentHeaderSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (parentHeaderSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (parentHeaderSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (parentHeaderSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   parentHeaderInputPointer args ↦ₘ∗ parentHeaderInputBytes args ∗
   (parentHeaderStackPointer args - parentHeaderFrameBytes) ↦ₘ? parentHeaderFrameBytes ∗
   (parentHeaderStackPointer args - parentHeaderFrameBytes - parentHeaderCalleeBytes) ↦ₘ?
     parentHeaderCalleeBytes ∗ True)%I.

Definition parentHeaderExitResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) (after : ParentHeaderOutcome) : iProp Sigma :=
  (parentHeaderResultPointer args ↦ₘ∗ parentHeaderAfterResult after ∗
   parentHeaderExitRegisterResources args)%I.

Definition parentHeaderResources `{!islaG Sigma} `{!threadG} (code : iProp Sigma) :
    IslarisContractResources ParentHeaderArgs ParentHeaderOutcome :=
  {| islarisCode := code;
     islarisEntry := parentHeaderEntryResources;
     islarisExit := parentHeaderExitResources |}.

Definition parentHeaderDomainAt (returnAddress : Z) (args : ParentHeaderArgs) : Prop :=
  parentHeaderReturnAddress args = returnAddress /\ parentHeaderArgsWellFormed args.
