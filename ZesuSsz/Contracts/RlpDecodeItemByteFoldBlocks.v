From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

Import ListNotations.
Open Scope Z_scope.

Definition decodeItemFoldInitPc (isList : bool) : Z :=
  if isList then 0x800d6ab4 else 0x800d6a14.
Definition decodeItemFoldExitPc (isList : bool) : Z :=
  if isList then 0x800d6ad8 else 0x800d6a38.
Definition decodeItemFoldSuccessPc (isList : bool) : Z :=
  if isList then 0x800d6b08 else 0x800d6a40.

Definition decodeItemFoldLengthFits (args : DecodeItemArgs)
    (n : Z) (lengthBytes : list byte) : bool :=
  Z.leb
    (bv_unsigned (Z_to_bv 64 (bigEndian lengthBytes + n + 1)))
    (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))).

(* The four initialization instructions clear a3, advance a4 and a5,
   and set a1 to the first byte after the long-length header. *)
Definition decodeItemFoldInitResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits oldAcc ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 n) ∗
   "x15" ↦ᵣ RVal_Bits oldCursor ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗ True)%I.

(* The length check changes a4 from n+1 to the wrapped machine sum.
   The next block decides whether the result is written or rejected. *)
Definition decodeItemFoldCheckedResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bigEndian lengthBytes)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bigEndian lengthBytes + n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n n payloadStart lengthBytes⌝ ∗ True)%I.

(* These are pending machine proofs. Each block gets the selected code
   lookup from Q40 and the exact Q20 header resources. The only loop
   arithmetic rewrite needed for preservation is zesu_bigEndian_snoc. *)
Definition decodeItemFoldEntryObligation `{!islaG Sigma} `{!threadG}
    (isList : bool) (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64) : iProp Sigma :=
  (decodeItemSelectedCode -∗
   instr_body (decodeItemFoldInitPc isList)
     (decodeItemFoldInitResources args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded ∗
      instr_pre (decodeItemByteFoldHeader isList)
        (decodeItemByteFoldResources args isList n 0 payloadStart
           lengthBytes frameBytes loaded ∗ True) ∗ True))%I.

Definition decodeItemFoldPreservationObligation `{!islaG Sigma} `{!threadG}
    (isList : bool) (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (next : byte) : iProp Sigma :=
  (decodeItemSelectedCode -∗
   instr_body (decodeItemByteFoldHeader isList)
     (⌜i < n /\ nth_error lengthBytes (Z.to_nat i) = Some next⌝ ∗
      decodeItemByteFoldResources args isList n i payloadStart
        lengthBytes frameBytes loaded ∗
      (if Z_lt_dec (i + 1) n then
         instr_pre (decodeItemByteFoldHeader isList)
           (decodeItemByteFoldResources args isList n (i + 1) payloadStart
              lengthBytes frameBytes (Z_to_bv 64 (bv_unsigned next)) ∗ True)
       else
         instr_pre (decodeItemFoldExitPc isList)
           (⌜(i + 1 = n)%Z⌝ ∗
            decodeItemByteFoldResources args isList n (i + 1) payloadStart
              lengthBytes frameBytes (Z_to_bv 64 (bv_unsigned next)) ∗ True)) ∗
      True))%I.

Definition decodeItemFoldExitObligation `{!islaG Sigma} `{!threadG}
    (isList : bool) (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (decodeItemSelectedCode -∗
   instr_body (decodeItemFoldExitPc isList)
     (decodeItemByteFoldResources args isList n n payloadStart
        lengthBytes frameBytes loaded ∗
      (if decodeItemFoldLengthFits args n lengthBytes then
         instr_pre (decodeItemFoldSuccessPc isList)
           (decodeItemFoldCheckedResources args n payloadStart
              lengthBytes frameBytes loaded ∗ True)
       else
         instr_pre 0x800d6ae0
           (decodeItemFoldCheckedResources args n payloadStart
              lengthBytes frameBytes loaded ∗ True)) ∗ True))%I.

