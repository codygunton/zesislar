(* Unfold markers for the shared helpers of ZesuSsz.Contracts.NextUint64BlockEntries. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Local Open Scope Z_scope.
#[export] Instance nextUint64Registers_unfold : LithiumUnfold (@nextUint64Registers) := I.
#[export] Typeclasses Opaque nextUint64Registers.
#[export] Instance nextUint64PostMemory_unfold : LithiumUnfold (@nextUint64PostMemory) := I.
#[export] Typeclasses Opaque nextUint64PostMemory.
