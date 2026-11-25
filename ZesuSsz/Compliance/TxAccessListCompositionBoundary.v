(* The boundary terms of the txAccessList block composition.
   TxAccessListBlockObligations.v (generated) and
   TxAccessListGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Interfaces.KeysToOwnedSlice.
Require Import ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Local Open Scope Z_scope.

(* The contract's postcondition at the return address. *)
Definition txAccessListPost `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (returnAddress : Z) : iProp Sigma :=
  (∃ outcome : TxAccessListOutcome,
    ⌜islarisContractAllows _ _ (txAccessListContractModel returnAddress) args outcome⌝ ∗
    txAccessListExitResources args outcome)%I.
Global Instance : LithiumUnfold (@txAccessListPost) := I.
Global Typeclasses Opaque txAccessListPost.

(* Every table entry carries it as K: the contract postcondition at
   returnAddress. The return slots of the function return jump there; each of
   their callers takes the generated return package as its premise, which the
   composition derives from K by that package's end bridge. *)
Definition txAccessListContinuation `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress (txAccessListPost args returnAddress).
Global Instance : LithiumUnfold (@txAccessListContinuation) := I.
Global Typeclasses Opaque txAccessListContinuation.

(* The table code: the own code and the callee specifications at their
   entries. The composition derives the four proved callees' specifications
   from their selected codes and compliance theorems, the allocator and memcpy
   premises from the contract code. *)
Definition txAccessListTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (txAccessListSelectedCode ∗
   □ instr_pre sym_rlp_decodeItem decodeItemCallSpec2 ∗
   □ instr_pre sym_array_list_Aligned_32_u8_null_ensureTotalCapacity keysEnsureCapacityCallSpec2 ∗
   □ instr_pre sym_array_list_Aligned_32_u8_null_toOwnedSlice keysToOwnedSliceCallSpec2 ∗
   □ instr_pre sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice entriesToOwnedSliceCallSpec2 ∗
   □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec ∗
   □ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Global Instance : LithiumUnfold (@txAccessListTableCode) := I.
Global Typeclasses Opaque txAccessListTableCode.

(* A block statement tagged with its block address and its entry constant;
   the composition selects the statement of a table slot by both tags. *)
Definition txAccessListBlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
