From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Automation.ByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.IslarisCode.
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

Lemma decodeItemByteFoldFirstGuard (args : DecodeItemArgs)
    (n payloadStart : Z) (lengthBytes : list byte) :
  decodeItemByteFoldFacts args n 0 payloadStart lengthBytes -> 0 < n.
Proof. unfold decodeItemByteFoldFacts; lia. Qed.

(* The taken bne compares the incremented a5 with a1. The input layout
   rules out address wrap on the next header visit. *)
Lemma decodeItemByteFoldBackedgeGuard (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte) :
  decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  i < n ->
  (Z_to_bv 64 (payloadStart + i) + Z_to_bv 64 1)%bv <>
    Z_to_bv 64 (payloadStart + n) ->
  i + 1 < n /\ 0 <= payloadStart + i + 1 < word64Modulus.
Proof.
  intros Hdomain Hfold Hguard Hbne.
  assert (Hnext : i + 1 < n).
  { unfold decodeItemByteFoldFacts in Hfold.
    destruct Hfold as (_ & Hi & _).
    assert (i + 1 <> n).
    { intro Heq. apply Hbne.
      rewrite Z_to_bv_add. f_equal. lia. }
    lia. }
  split; [exact Hnext|].
  unfold decodeItemByteFoldFacts in Hfold.
  destruct Hfold as (_ & Hi & Hstart & _ & _ & Hfit).
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hdomain.
  destruct Hdomain as (_ & _ & Hlayout).
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as (Hinput & _ & Hnowrap & _).
  unfold word64Modulus in *.
  lia.
Qed.

(* The caller's input and result arrays remain owned at both headers.
   frameBytes are the 16 bytes after the prologue saves ra and s0.
   The frame-content relation remains a block proof obligation. *)
Definition decodeItemByteFoldResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (isList : bool) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
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
