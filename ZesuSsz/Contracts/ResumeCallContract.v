From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Open Scope Z_scope.

(* W0 held-out entry interface for opcodes.call.resumeCall (entry 0x800aaec8).
   Entry interface only: registers, memory footprints, stack frame, ranges,
   separations, the word links of the pointers that the function loads, and a
   domain, from the calling convention, the caller sites and the object's
   DWARF layouts. It states no meaning of the result. The source of each fact
   is in the W0 justification table of the held-out run record. *)

Notation resumeCallStackBytes := ((16) : Z) (only parsing).
Notation resumeCallInterpreterSize := ((688) : Z) (only parsing).
Notation resumeCallCallResultSize := ((72) : Z) (only parsing).
Notation resumeCallStackElementBytes := ((32) : Z) (only parsing).
Notation resumeCallStackLow := ((0xa0000000) : Z) (only parsing).
Notation resumeCallStackHigh := ((0xa0400000) : Z) (only parsing).
Notation resumeCallRamLow := ((0xa0000000) : Z) (only parsing).
Notation resumeCallRamHigh := ((0xc0000000) : Z) (only parsing).
Notation resumeCallReturnDataPointerField := ((0) : Z) (only parsing).
Notation resumeCallReturnDataLengthField := ((8) : Z) (only parsing).
Notation resumeCallStackDataField := ((568) : Z) (only parsing).
Notation resumeCallStackCapacityField := ((576) : Z) (only parsing).
Notation resumeCallMemoryPointerField := ((624) : Z) (only parsing).
Notation resumeCallMemoryLengthField := ((632) : Z) (only parsing).

Record ResumeCallArgs : Type := {
  resumeCallInterpreterPointer : Z;
  resumeCallBeforeInterpreter : list byte;
  resumeCallCallResultPointer : Z;
  resumeCallCallResultBytes : list byte;
  resumeCallReturnDataPointer : Z;
  resumeCallReturnDataLength : Z;
  resumeCallReturnDataBytes : list byte;
  resumeCallMemoryPointer : Z;
  resumeCallMemoryLength : Z;
  resumeCallBeforeMemory : list byte;
  resumeCallStackDataPointer : Z;
  resumeCallStackCapacity : Z;
  resumeCallBeforeStackData : list byte;
  resumeCallReturnOffset : Z;
  resumeCallReturnSize : Z;
  resumeCallNewAccountStateGas : bv 64;
  resumeCallStackPointer : Z;
  resumeCallReturnAddress : Z;
  resumeCallSavedFramePointer : bv 64
}.

Record ResumeCallOutcome : Type := {
  resumeCallAfterInterpreter : list byte;
  resumeCallAfterMemory : list byte;
  resumeCallAfterStackData : list byte
}.

(* The little-endian 64-bit word at a byte offset of an owned object. *)
Definition resumeCallWordAt (bytes : list byte) (offset : Z) : Z :=
  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).

Definition resumeCallSeparate (p n q m : Z) : Prop :=
  p + n <= q \/ q + m <= p.

Definition resumeCallArgsWellFormed (args : ResumeCallArgs) : Prop :=
  length (resumeCallBeforeInterpreter args) = 688%nat /\
  length (resumeCallCallResultBytes args) = 72%nat /\
  0 <= resumeCallReturnDataLength args < 2 ^ 64 /\
  Z.of_nat (length (resumeCallReturnDataBytes args)) = resumeCallReturnDataLength args /\
  0 <= resumeCallMemoryLength args < 2 ^ 64 /\
  Z.of_nat (length (resumeCallBeforeMemory args)) = resumeCallMemoryLength args /\
  0 <= resumeCallStackCapacity args /\
  Z.of_nat (length (resumeCallBeforeStackData args)) =
    resumeCallStackElementBytes * resumeCallStackCapacity args /\
  0 <= resumeCallReturnOffset args < 2 ^ 64 /\
  0 <= resumeCallReturnSize args < 2 ^ 64 /\
  resumeCallReturnOffset args + resumeCallReturnSize args <= resumeCallMemoryLength args /\
  resumeCallWordAt (resumeCallCallResultBytes args) resumeCallReturnDataPointerField =
    resumeCallReturnDataPointer args /\
  resumeCallWordAt (resumeCallCallResultBytes args) resumeCallReturnDataLengthField =
    resumeCallReturnDataLength args /\
  resumeCallWordAt (resumeCallBeforeInterpreter args) resumeCallStackDataField =
    resumeCallStackDataPointer args /\
  resumeCallWordAt (resumeCallBeforeInterpreter args) resumeCallStackCapacityField =
    resumeCallStackCapacity args /\
  resumeCallWordAt (resumeCallBeforeInterpreter args) resumeCallMemoryPointerField =
    resumeCallMemoryPointer args /\
  resumeCallWordAt (resumeCallBeforeInterpreter args) resumeCallMemoryLengthField =
    resumeCallMemoryLength args /\
  resumeCallRamLow <= resumeCallInterpreterPointer args /\
  resumeCallInterpreterPointer args + resumeCallInterpreterSize <= resumeCallRamHigh /\
  resumeCallStackLow <= resumeCallCallResultPointer args /\
  resumeCallCallResultPointer args + resumeCallCallResultSize <= resumeCallStackHigh /\
  (0 < resumeCallReturnDataLength args ->
   resumeCallRamLow <= resumeCallReturnDataPointer args /\
   resumeCallReturnDataPointer args + resumeCallReturnDataLength args <= resumeCallRamHigh) /\
  (0 < resumeCallMemoryLength args ->
   resumeCallRamLow <= resumeCallMemoryPointer args /\
   resumeCallMemoryPointer args + resumeCallMemoryLength args <= resumeCallRamHigh) /\
  resumeCallRamLow <= resumeCallStackDataPointer args /\
  resumeCallStackDataPointer args + resumeCallStackElementBytes * resumeCallStackCapacity args <=
    resumeCallRamHigh /\
  resumeCallStackLow + resumeCallStackBytes <= resumeCallStackPointer args <= resumeCallStackHigh /\
  resumeCallStackPointer args mod 16 = 0 /\
  0 <= resumeCallReturnAddress args < 2 ^ 64 /\ resumeCallReturnAddress args mod 4 = 0 /\
  resumeCallSeparate (resumeCallInterpreterPointer args) resumeCallInterpreterSize
    (resumeCallCallResultPointer args) resumeCallCallResultSize /\
  resumeCallSeparate (resumeCallInterpreterPointer args) resumeCallInterpreterSize
    (resumeCallReturnDataPointer args) (resumeCallReturnDataLength args) /\
  resumeCallSeparate (resumeCallInterpreterPointer args) resumeCallInterpreterSize
    (resumeCallMemoryPointer args) (resumeCallMemoryLength args) /\
  resumeCallSeparate (resumeCallInterpreterPointer args) resumeCallInterpreterSize
    (resumeCallStackDataPointer args) (resumeCallStackElementBytes * resumeCallStackCapacity args) /\
  resumeCallSeparate (resumeCallInterpreterPointer args) resumeCallInterpreterSize
    (resumeCallStackPointer args - resumeCallStackBytes) resumeCallStackBytes /\
  resumeCallSeparate (resumeCallCallResultPointer args) resumeCallCallResultSize
    (resumeCallReturnDataPointer args) (resumeCallReturnDataLength args) /\
  resumeCallSeparate (resumeCallCallResultPointer args) resumeCallCallResultSize
    (resumeCallMemoryPointer args) (resumeCallMemoryLength args) /\
  resumeCallSeparate (resumeCallCallResultPointer args) resumeCallCallResultSize
    (resumeCallStackDataPointer args) (resumeCallStackElementBytes * resumeCallStackCapacity args) /\
  resumeCallSeparate (resumeCallCallResultPointer args) resumeCallCallResultSize
    (resumeCallStackPointer args - resumeCallStackBytes) resumeCallStackBytes /\
  resumeCallSeparate (resumeCallReturnDataPointer args) (resumeCallReturnDataLength args)
    (resumeCallMemoryPointer args) (resumeCallMemoryLength args) /\
  resumeCallSeparate (resumeCallReturnDataPointer args) (resumeCallReturnDataLength args)
    (resumeCallStackDataPointer args) (resumeCallStackElementBytes * resumeCallStackCapacity args) /\
  resumeCallSeparate (resumeCallReturnDataPointer args) (resumeCallReturnDataLength args)
    (resumeCallStackPointer args - resumeCallStackBytes) resumeCallStackBytes /\
  resumeCallSeparate (resumeCallMemoryPointer args) (resumeCallMemoryLength args)
    (resumeCallStackDataPointer args) (resumeCallStackElementBytes * resumeCallStackCapacity args) /\
  resumeCallSeparate (resumeCallMemoryPointer args) (resumeCallMemoryLength args)
    (resumeCallStackPointer args - resumeCallStackBytes) resumeCallStackBytes /\
  resumeCallSeparate (resumeCallStackDataPointer args)
    (resumeCallStackElementBytes * resumeCallStackCapacity args)
    (resumeCallStackPointer args - resumeCallStackBytes) resumeCallStackBytes.

Definition resumeCallEntryResources `{!islaG Sigma} `{!threadG}
    (args : ResumeCallArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (resumeCallSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallInterpreterPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallCallResultPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallReturnOffset args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallReturnSize args)) ∗
   "x14" ↦ᵣ RVal_Bits (resumeCallNewAccountStateGas args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   resumeCallInterpreterPointer args ↦ₘ∗ resumeCallBeforeInterpreter args ∗
   resumeCallCallResultPointer args ↦ₘ∗ resumeCallCallResultBytes args ∗
   resumeCallReturnDataPointer args ↦ₘ∗ resumeCallReturnDataBytes args ∗
   resumeCallMemoryPointer args ↦ₘ∗ resumeCallBeforeMemory args ∗
   resumeCallStackDataPointer args ↦ₘ∗ resumeCallBeforeStackData args ∗
   (resumeCallStackPointer args - resumeCallStackBytes) ↦ₘ? resumeCallStackBytes ∗
   ⌜resumeCallArgsWellFormed args⌝ ∗ True)%I.

Definition resumeCallExitRegisterResources `{!islaG Sigma} `{!threadG}
    (args : ResumeCallArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (resumeCallSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (resumeCallInterpreterPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   resumeCallCallResultPointer args ↦ₘ∗ resumeCallCallResultBytes args ∗
   resumeCallReturnDataPointer args ↦ₘ∗ resumeCallReturnDataBytes args ∗
   (resumeCallStackPointer args - resumeCallStackBytes) ↦ₘ? resumeCallStackBytes ∗ True)%I.

Definition resumeCallExitResources `{!islaG Sigma} `{!threadG}
    (args : ResumeCallArgs) (after : ResumeCallOutcome) : iProp Sigma :=
  (resumeCallInterpreterPointer args ↦ₘ∗ resumeCallAfterInterpreter after ∗
   resumeCallMemoryPointer args ↦ₘ∗ resumeCallAfterMemory after ∗
   resumeCallStackDataPointer args ↦ₘ∗ resumeCallAfterStackData after ∗
   resumeCallExitRegisterResources args)%I.

Definition resumeCallResources `{!islaG Sigma} `{!threadG} (code : iProp Sigma) :
    IslarisContractResources ResumeCallArgs ResumeCallOutcome :=
  {| islarisCode := code;
     islarisEntry := resumeCallEntryResources;
     islarisExit := resumeCallExitResources |}.

Definition resumeCallDomainAt (returnAddress : Z) (args : ResumeCallArgs) : Prop :=
  resumeCallReturnAddress args = returnAddress /\ resumeCallArgsWellFormed args.
