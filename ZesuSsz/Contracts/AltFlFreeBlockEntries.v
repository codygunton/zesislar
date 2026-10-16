From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Import ListNotations.
Open Scope Z_scope.

Definition freeSavedFrameFacts (args : FreeArgs) (frameBytes : list byte) : Prop :=
  frameBytes = (word64Bytes (bv_unsigned (freeSavedFramePointer args)) ++
    word64Bytes (freeReturnAddress args))%list.

Definition freeCaller `{!islaG Sigma} `{!threadG} (args : FreeArgs) : iProp Sigma :=
  instr_pre (freeReturnAddress args)
    (∃ (bufferBytes listBytes : list byte),
     freeBufferPointer args ↦ₘ∗ bufferBytes ∗ freeListsPointer ↦ₘ∗ listBytes ∗
     ⌜freeAllowsAt (freeReturnAddress args) args
       {| freeAfterBuffer := bufferBytes; freeAfterLists := listBytes |}⌝ ∗
     freeExitRegisterResources args).

(* The negative subtraction wraps in the register before the small-alignment guard. *)
Definition freeAlignmentWord (args : FreeArgs) : bv 64 :=
  Z_to_bv 64 (freeLog2Alignment args - 3).
Definition freeCandidateClass (args : FreeArgs) : Z :=
  Z.max (freeSizeClassOfBytes (freeBufferLength args))
    (bv_unsigned (freeAlignmentWord args)).

Definition freeBlockFacts (pc : Z) (args : FreeArgs)
    (x10 x12 x13 x14 : bv 64) : Prop :=
  let size := freeBufferLength args in
  let alignment := freeLog2Alignment args in
  let sizeClass := freeSizeClassOfBytes size in
  match pc with
  | 0x80041f58 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 0 <= bv_unsigned x12 <= 2048
  | 0x80041f60 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 0 <= bv_unsigned x12 <= 64
  | 0x80041f68 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 0 <= bv_unsigned x12 <= 16
  | 0x80041f80 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 2049 <= bv_unsigned x12
  | 0x80041f8c => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 2049 <= bv_unsigned x12 <= 262144
  | 0x80041f98 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 2049 <= bv_unsigned x12 <= 16384
  | 0x80041fa4 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 2049 <= bv_unsigned x12 <= 4096
  | 0x80041fb8 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 65 <= bv_unsigned x12 <= 2048
  | 0x80041fc0 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 65 <= bv_unsigned x12 <= 512
  | 0x80041fc8 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 65 <= bv_unsigned x12 <= 128
  | 0x80041fdc => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 262145 <= bv_unsigned x12
  | 0x80041fe8 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 262145 <= bv_unsigned x12 <= 4194304
  | 0x80041ff4 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 262145 <= bv_unsigned x12 <= 1048576
  | 0x80042014 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 17 <= bv_unsigned x12 <= 64
  | 0x8004202c => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 16385 <= bv_unsigned x12 <= 262144
  | 0x80042038 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 16385 <= bv_unsigned x12 <= 65536
  | 0x80042058 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 513 <= bv_unsigned x12 <= 2048
  | 0x80042074 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 4194305 <= bv_unsigned x12
  | 0x80042080 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 4194305 <= bv_unsigned x12 <= 8388608
  | 0x80042094 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 4097 <= bv_unsigned x12 <= 16384
  | 0x800420b4 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 129 <= bv_unsigned x12 <= 512
  | 0x800420d0 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 1048577 <= bv_unsigned x12 <= 4194304
  | 0x800420f0 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 65537 <= bv_unsigned x12 <= 262144
  | 0x80042110 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 size /\ 8388609 <= bv_unsigned x12
  | 0x80041f7c => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80041fb4 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80041fd8 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042010 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042028 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042054 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042070 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042090 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x800420b0 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x800420cc => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x800420ec => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x8004210c => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x13 = x12 /\ x14 = freeAlignmentWord args /\ bv_unsigned x14 < bv_unsigned x12
  | 0x80042130 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x14 = freeAlignmentWord args /\ bv_unsigned x12 <= bv_unsigned x14
  | 0x80042134 => x10 = Z_to_bv 64 alignment /\ x12 = Z_to_bv 64 sizeClass /\
      x14 = freeAlignmentWord args /\ x13 = Z_to_bv 64 (freeCandidateClass args)
  | 0x8004213c => x10 = Z_to_bv 64 alignment /\ 3 < alignment /\
      x12 = Z_to_bv 64 sizeClass /\ x13 = Z_to_bv 64 (freeSizeClass size alignment) /\
      x14 = freeAlignmentWord args
  | 0x80042144 => x10 = Z_to_bv 64 22 /\
      freeListCount <= freeSizeClass size alignment
  | 0x80042154 => x10 = Z_to_bv 64 alignment /\ alignment <= 3 /\
      x12 = Z_to_bv 64 sizeClass
  | 0x80042160 => x10 = Z_to_bv 64 22 /\
      x13 = Z_to_bv 64 (freeSizeClass size alignment) /\
      0 <= freeSizeClass size alignment < freeListCount
  | _ => False
  end.

Definition freeBlockCore `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits x1 ∗ "x2" ↦ᵣ RVal_Bits x2 ∗
   "x8" ↦ᵣ RVal_Bits x8 ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   freeBufferPointer args ↦ₘ∗ bufferBytes ∗
   freeListsPointer ↦ₘ∗ listBytes ∗
   (freeStackPointer args - freeStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜freeArgsWellFormed args /\
     x1 = Z_to_bv 64 (freeReturnAddress args) /\
     x2 = Z_to_bv 64 (freeStackPointer args - freeStackBytes) /\
     x8 = Z_to_bv 64 (freeStackPointer args) /\
     x11 = Z_to_bv 64 (freeBufferPointer args) /\
     bufferBytes = freeBeforeBuffer args /\ listBytes = freeBeforeLists args /\
     freeSavedFrameFacts args frameBytes⌝ ∗ freeCaller args ∗ True)%I.

Definition freeEntryAt80041f38 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes : list byte) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits x1 ∗ "x2" ↦ᵣ RVal_Bits x2 ∗
   "x8" ↦ᵣ RVal_Bits x8 ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   freeBufferPointer args ↦ₘ∗ bufferBytes ∗ freeListsPointer ↦ₘ∗ listBytes ∗
   (freeStackPointer args - freeStackBytes) ↦ₘ? freeStackBytes ∗
   ⌜freeArgsWellFormed args /\ x1 = Z_to_bv 64 (freeReturnAddress args) /\
     x2 = Z_to_bv 64 (freeStackPointer args) /\ x8 = freeSavedFramePointer args /\
     x11 = Z_to_bv 64 (freeBufferPointer args) /\
     x12 = Z_to_bv 64 (freeBufferLength args) /\
     x13 = Z_to_bv 64 (freeLog2Alignment args) /\
     bufferBytes = freeBeforeBuffer args /\ listBytes = freeBeforeLists args⌝ ∗
   freeCaller args ∗ True)%I.

Definition freeEntryAt80041f58 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f58 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f60 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f60 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f68 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f68 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f7c `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f7c args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f80 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f80 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f8c `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f8c args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041f98 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041f98 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fa4 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fa4 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fb4 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fb4 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fb8 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fb8 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fc0 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fc0 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fc8 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fc8 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fd8 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fd8 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fdc `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fdc args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041fe8 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041fe8 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80041ff4 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80041ff4 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042010 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042010 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042014 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042014 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042028 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042028 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt8004202c `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x8004202c args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042038 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042038 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042054 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042054 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042058 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042058 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042070 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042070 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042074 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042074 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042080 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042080 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042090 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042090 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042094 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042094 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420b0 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420b0 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420b4 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420b4 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420cc `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420cc args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420d0 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420d0 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420ec `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420ec args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt800420f0 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x800420f0 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt8004210c `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x8004210c args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042110 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042110 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042130 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042130 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042134 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042134 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt8004213c `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x8004213c args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042144 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042144 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042154 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042154 args x10 x12 x13 x14⌝)%I.

Definition freeEntryAt80042160 `{!islaG Sigma} `{!threadG} (args : FreeArgs)
    (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) : iProp Sigma :=
  (freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ∗
   ⌜freeBlockFacts 0x80042160 args x10 x12 x13 x14⌝)%I.

