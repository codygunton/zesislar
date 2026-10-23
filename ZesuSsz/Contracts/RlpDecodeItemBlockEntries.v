From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Import ListNotations.
Open Scope Z_scope.

(* The six return entries retain the caller's arrays and saved frame.
   Other caller-saved registers remain symbolic until each block proof. *)
Record DecodeItemReturnLocals : Type := {
  returnA1 : bv 64;
  returnA2 : bv 64;
  returnA3 : bv 64;
  returnA4 : bv 64;
  returnA5 : bv 64;
  returnA6 : bv 64;
  returnStorage : list byte;
  returnFrame : list byte
}.

Definition decodeItemReturnEntryCore `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (returnA1 locals) ∗
   "x12" ↦ᵣ RVal_Bits (returnA2 locals) ∗
   "x13" ↦ᵣ RVal_Bits (returnA3 locals) ∗
   "x14" ↦ᵣ RVal_Bits (returnA4 locals) ∗
   "x15" ↦ᵣ RVal_Bits (returnA5 locals) ∗
   "x16" ↦ᵣ RVal_Bits (returnA6 locals) ∗
   "x2" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ returnStorage locals ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ returnFrame locals ∗
   ⌜decodeItemDomainAt (decodeItemReturnAddress args)
       decodeItemC1BDomain args /\
     decodeItemSavedFrameFacts args (returnFrame locals) /\
     length (returnStorage locals) = 40%nat⌝ ∗
   decodeItemBranchContinuation args ∗ True)%I.

(* This join follows the literal and short-string writes to fields 0, 8,
   and 32. The block writes fields 16 and 24 before returning. *)
Definition decodeItem698cCaseResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) (isLiteral : bool) : iProp Sigma :=
  (decodeItemReturnEntryCore args locals ∗
   ⌜decodeItemInputHead args inputPrefix rest /\
     (if isLiteral then bv_unsigned inputPrefix <= 127
      else 129 <= bv_unsigned inputPrefix <= 183) /\
     bv_unsigned (returnA1 locals) = (decodeItemInputPointer args +
       (if isLiteral then 0 else 1))%Z /\
     littleEndian lengthBytes =
       (if isLiteral then 1 else bv_unsigned inputPrefix - 128) /\
     bv_unsigned (returnA2 locals) =
       (if isLiteral then 1 else (1 + (bv_unsigned inputPrefix - 128))%Z) /\
     decodeItemAcceptedFacts args false (if isLiteral then 0 else 1)
       (if isLiteral then 1 else bv_unsigned inputPrefix - 128) /\
     fieldImage (returnStorage locals) 0 pointerBytes /\
     fieldImage (returnStorage locals) 8 lengthBytes /\
     fieldImage (returnStorage locals) 32 [Z_to_bv 8 0; Z_to_bv 8 0] /\
     pointerBytes = word64Bytes (bv_unsigned (returnA1 locals)) /\
     length lengthBytes = 8%nat /\
     preservedImage (decodeItemBeforeStorage args) (returnStorage locals) 17 7 /\
     preservedImage (decodeItemBeforeStorage args) (returnStorage locals) 34 6⌝)%I.

(* Public join entries bind machine registers and complete byte arrays. *)

(* Every return target is the caller's address. The Q44 image fixes all
   40 result bytes, including the preserved padding on success. *)
Definition decodeItemReturnOkExit `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (pointer length consumed : Z)
    (isList : bool) : iProp Sigma :=
  instr_pre (decodeItemReturnAddress args)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      DecodeMeaningModuloKnownBugs args
        (decodeItemOkBytes (decodeItemBeforeStorage args)
          (word64Bytes pointer) (word64Bytes length)
          (word64Bytes consumed) isList)⌝ ∗
     decodeItemExitResources args
       (decodeItemOkBytes (decodeItemBeforeStorage args)
          (word64Bytes pointer) (word64Bytes length)
          (word64Bytes consumed) isList) ∗ True).

Definition decodeItemReturnErrorExit `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  instr_pre (decodeItemReturnAddress args)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      DecodeMeaningModuloKnownBugs args errorEncoding⌝ ∗
     decodeItemExitResources args errorEncoding ∗ True).

(* Each statement is a pending machine block proof. Its postcondition is
   the Q44 complete result image at the caller's return address. *)
Definition decodeItemReturnBlockObligation `{!islaG Sigma} `{!threadG}
    (pc : Z) (entry exit : iProp Sigma) : iProp Sigma :=
  (decodeItemSelectedCode -∗
   instr_body pc (entry ∗ exit ∗ True))%I.
