From Coq Require Import Lia ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Open Scope Z_scope.



Definition decodeItemErrorBranchEntry `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (masked : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     129 <= bv_unsigned inputPrefix <= 183 /\
     bv_unsigned masked = bv_unsigned inputPrefix - 128 /\
     bv_unsigned masked >=
     bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))⌝ ∗
   "x13" ↦ᵣ RVal_Bits masked ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.
