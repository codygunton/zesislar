(* The boundary terms of the keysEnsureCapacity block composition.
   KeysEnsureCapacityBlockObligations.v (generated) and
   KeysEnsureCapacityGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Local Open Scope Z_scope.

(* The contract's postcondition at the return address. *)
Definition keysEnsureCapacityPost `{!islaG Sigma} `{!threadG}
    (base : EnsureCapacityArgs) (returnAddress : Z) : iProp Sigma :=
  (∃ outcome : EnsureCapacityOutcome,
    ⌜islarisContractAllows _ _ (keysEnsureCapacityContractModel returnAddress) base outcome⌝ ∗
    keysEnsureCapacityExit base outcome)%I.

(* Every table entry carries it as K: the contract postcondition at
   returnAddress. The three return slots of the duplicated join 0x008c jump
   there; each of their callers takes the generated return package as its
   premise, which the composition derives from K by its end bridge. *)
Definition keysEnsureCapacityContinuation `{!islaG Sigma} `{!threadG}
    (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress (keysEnsureCapacityPost (ensureBase args) returnAddress).
Global Instance : LithiumUnfold (@keysEnsureCapacityContinuation) := I.
Global Typeclasses Opaque keysEnsureCapacityContinuation.

(* The table code: the own code and the callee premises of the contract. *)
Definition keysEnsureCapacityTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysEnsureCapacitySelectedCode ∗ □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec ∗
   □ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityTableCode) := I.
Global Typeclasses Opaque keysEnsureCapacityTableCode.

(* A block statement tagged with its block address and its entry constant;
   the composition selects the statement of a table slot by both tags. *)
Definition keysEnsureCapacityBlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
