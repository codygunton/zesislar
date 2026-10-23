From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.

Import ListNotations.
Open Scope Z_scope.

(* The native family returns the caller registers required by the compositional exit. *)
Definition decodeItemBranchContinuationAt `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) : iProp Sigma :=
  (instr_pre returnAddress
    (∃ outcome : DecodeItemOutcome,
      decodeItemExitResourcesRegisters args outcome ∗
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝))%I.

Definition decodeItemBranchContinuation `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  decodeItemBranchContinuationAt args (decodeItemReturnAddress args).


Definition decodeItemSavedFrameFacts (args : DecodeItemArgs)
    (frameBytes : list byte) : Prop :=
  length frameBytes = 16%nat /\
  word64At frameBytes 0 (bv_unsigned (decodeItemSavedFramePointer args)) /\
  word64At frameBytes 8 (decodeItemReturnAddress args).

(* All fifteen entries retain the input, the untouched output, and the
   initialized stack frame. The current a1 value is symbolic. *)
Definition decodeItemBranchBase `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x11 : bv 64) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x2" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜decodeItemSavedFrameFacts args frameBytes /\
     decodeItemDomainAt (decodeItemReturnAddress args)
       decodeItemC1BDomain args⌝ ∗
   decodeItemBranchContinuation args ∗ True)%I.

Local Notation "'dispatchEntry' args frameBytes x13 x14 inputPrefix rest facts" :=
  (∃ (x15 x16 : bv 64), ⌜decodeItemInputHead args inputPrefix rest /\ facts⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes (Z_to_bv 64 (decodeItemInputPointer args)))%I
  (at level 10, args, frameBytes, x13, x14, inputPrefix, rest, facts at level 9).

(* 0x800d6970: beq a2, zero, error. *)

(* 0x800d6978: blt a3, zero, high-prefix dispatch. *)

(* 0x800d69ac: bne a3, a4, short-string class test. *)

(* 0x800d69dc: bltu a4, a3, long-string dispatch. *)

(* 0x800d69e4: bgeu a3, a2, error. *)

(* 0x800d6a04: bgeu a3, a4, list dispatch. *)

(* The Q20 initialization resource fixes a4 to n and the input slice. *)

(* Q20 fixes both a5 and a1 to payloadStart+n at loop exit. *)

(* 0x800d6a68: bgeu a3, a4, long-list class test. *)
