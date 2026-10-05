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

Import ListNotations.
Open Scope Z_scope.

(* The continuation is the one supplied by the selected Level 1 contract. *)
Definition decodeItemBranchContinuationAt `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) : iProp Sigma :=
  (instr_pre returnAddress
    (∃ outcome : DecodeItemOutcome,
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝ ∗
      decodeItemExitResources args outcome))%I.

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

(* 0x800d6970: beq a2, zero, error. *)
Definition decodeItemEntryAt800d6974 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x13 x14 x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d6978: blt a3, zero, high-prefix dispatch. *)
Definition decodeItemEntryAt800d697c `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x14 x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     bv_unsigned inputPrefix <= 127 /\
     x13 = Z_to_bv 64 (bv_signed inputPrefix) /\
     decodeItemAcceptedFacts args false 0 1 /\
     0 <= bv_signed x13⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

Definition decodeItemEntryAt800d69a4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x14 x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     128 <= bv_unsigned inputPrefix <= 255 /\
     x13 = Z_to_bv 64 (bv_signed inputPrefix) /\
     bv_signed x13 < 0⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d69ac: bne a3, a4, short-string class test. *)
Definition decodeItemEntryAt800d69d8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     129 <= bv_unsigned inputPrefix <= 255 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     x13 <> Z_to_bv 64 128⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 128) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d69dc: bltu a4, a3, long-string dispatch. *)
Definition decodeItemEntryAt800d69e0 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     129 <= bv_unsigned inputPrefix <= 183 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned (Z_to_bv 64 183) >= bv_unsigned x13⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d69e4: bgeu a3, a2, error. *)
Definition decodeItemEntryAt800d69e8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     129 <= bv_unsigned inputPrefix <= 183 /\
     bv_unsigned x13 = bv_unsigned inputPrefix - 128 /\
     decodeItemAcceptedFacts args false 1 (bv_unsigned inputPrefix - 128) /\
     bv_unsigned x13 <
      bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

Definition decodeItemEntryAt800d6a00 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     184 <= bv_unsigned inputPrefix <= 255 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned (Z_to_bv 64 183) < bv_unsigned x13⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d6a04: bgeu a3, a4, list dispatch. *)
Definition decodeItemEntryAt800d6a08 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     184 <= bv_unsigned inputPrefix <= 191 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned x13 < bv_unsigned (Z_to_bv 64 192)⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 192) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* The Q20 initialization resource fixes a4 to n and the input slice. *)
Definition decodeItemEntryAt800d6a14 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (⌜decodeItemC1BDomain args /\
     decodeItemFoldProvenance args false
     inputPrefix rest n payloadStart lengthBytes /\
     bv_unsigned (Z_to_bv 64 n) <
      bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
    decodeItemSavedFrameFacts args frameBytes⌝ ∗
   decodeItemFoldInitResources args n payloadStart lengthBytes frameBytes
     oldAcc oldCursor loaded ∗
   decodeItemBranchContinuation args)%I.

(* Q20 fixes both a5 and a1 to payloadStart+n at loop exit. *)
Definition decodeItemEntryAt800d6a38 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (⌜decodeItemC1BDomain args /\
     decodeItemFoldProvenance args false
     inputPrefix rest n payloadStart lengthBytes /\
     decodeItemSavedFrameFacts args frameBytes⌝ ∗
   decodeItemByteFoldResources args false n n payloadStart
     lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args)%I.

Definition decodeItemEntryAt800d6a64 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     192 <= bv_unsigned inputPrefix <= 255 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned x13 >= bv_unsigned (Z_to_bv 64 192)⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 192) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

(* 0x800d6a68: bgeu a3, a4, long-list class test. *)
Definition decodeItemEntryAt800d6a6c `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     192 <= bv_unsigned inputPrefix <= 247 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned x13 < bv_unsigned (Z_to_bv 64 248)⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 248) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

Definition decodeItemEntryAt800d6aa8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (x13 : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     248 <= bv_unsigned inputPrefix <= 255 /\
     bv_unsigned x13 = bv_unsigned inputPrefix /\
     bv_unsigned x13 >= bv_unsigned (Z_to_bv 64 248)⌝ ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 248) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.

Definition decodeItemEntryAt800d6ab4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (⌜decodeItemC1BDomain args /\
     decodeItemFoldProvenance args true
     inputPrefix rest n payloadStart lengthBytes /\
     bv_unsigned (Z_to_bv 64 n) <
      bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
    decodeItemSavedFrameFacts args frameBytes⌝ ∗
   decodeItemFoldInitResources args n payloadStart lengthBytes frameBytes
     oldAcc oldCursor loaded ∗
   decodeItemBranchContinuation args)%I.

Definition decodeItemEntryAt800d6ad8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (⌜decodeItemC1BDomain args /\
     decodeItemFoldProvenance args true
     inputPrefix rest n payloadStart lengthBytes /\
     decodeItemSavedFrameFacts args frameBytes⌝ ∗
   decodeItemByteFoldResources args true n n payloadStart
     lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args)%I.

(* Pending machine bridge. The prologue must create the exact saved frame
   before the nonempty branch can supply its first successor entry. *)
Definition decodeItemPrologueTo6974Bridge : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG)
    (returnAddress : Z) (args : DecodeItemArgs),
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
    ⊢ (decodeItemSelectedCode -∗
       instr_body decodeItemEntry
         (decodeItemEntryResources
            (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
          decodeItemBranchContinuationAt args returnAddress ∗
          instr_pre 0x800d6974
            (∃ (frameBytes : list byte) (inputPrefix : byte) (rest : list byte),
              decodeItemEntryAt800d6974 args frameBytes inputPrefix rest ∗ True) ∗ True))%I.
