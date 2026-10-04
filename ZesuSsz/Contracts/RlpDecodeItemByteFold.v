From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Automation.ByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Import ListNotations.
Open Scope Z_scope.

(* The stock ELF has two headers: 0x800d6a24 for long strings and
   0x800d6ac4 for long lists. Both execute the same five instructions.
   At each header, a5 points at the next length byte. a1 points past
   the length bytes, and a3 holds the accumulated prefix. *)
Definition decodeItemByteFoldHeader (isList : bool) : Z :=
  if isList then 0x800d6ac4 else 0x800d6a24.

Definition decodeItemByteFoldFacts (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte) : Prop :=
  1 <= n <= 8 /\ 0 <= i <= n /\
  payloadStart = decodeItemInputPointer args + 1 /\
  lengthBytes = firstn (Z.to_nat n) (skipn 1 (decodeItemInputBytes args)) /\
  Z.of_nat (length lengthBytes) = n /\
  payloadStart + n <= decodeItemInputPointer args + decodeItemInputLength args.

(* The caller's input and result arrays remain owned at both headers.
   frameBytes are the 16 bytes after the prologue saves ra and s0.
   The frame-content relation remains a block proof obligation. *)
Definition decodeItemByteFoldResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (isList : bool) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes))) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + i)) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I.

Definition decodeItemByteFoldStringHeader `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  decodeItemByteFoldResources args false n i payloadStart lengthBytes frameBytes loaded.

Definition decodeItemByteFoldListHeader `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  decodeItemByteFoldResources args true n i payloadStart lengthBytes frameBytes loaded.
