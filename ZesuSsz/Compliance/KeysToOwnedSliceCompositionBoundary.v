(* The boundary terms of the keysToOwnedSlice block composition.
   KeysToOwnedSliceBlockObligations.v (generated) and
   KeysToOwnedSliceGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Local Open Scope Z_scope.

(* The contract continuation of KeysToOwnedSliceContractCorrect at
   returnAddress. Every table entry carries it as K; a block that reaches the
   return consumes it through the return package's end bridge. *)
Definition keysToOwnedSliceContinuation `{!islaG Sigma} `{!threadG}
    (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress (∃ outcome : ToOwnedSliceOutcome,
    ⌜bv_unsigned (toOwnedReturnAddress (keysBase args)) = returnAddress /\
      toOwnedSliceDomain keysElementBytes (keysBase args) /\
      toOwnedSliceAllows keysElementBytes keysEmptyPointer (keysBase args) outcome⌝ ∗
    toOwnedSliceExit keysElementBytes keysLog2Alignment (keysBase args) outcome).
Global Instance : LithiumUnfold (@keysToOwnedSliceContinuation) := I.
Global Typeclasses Opaque keysToOwnedSliceContinuation.

(* The table code: the own code and the four callee specs at their entries
   (the allocator's alloc, remap and free, and memcpy). *)
Definition keysToOwnedSliceTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysToOwnedSliceSelectedCode ∗
   □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec ∗
   □ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Global Instance : LithiumUnfold (@keysToOwnedSliceTableCode) := I.
Global Typeclasses Opaque keysToOwnedSliceTableCode.

(* A block statement tagged with its block address and its entry constant;
   the composition selects the statement of a table slot by both tags. *)
Definition keysToOwnedSliceBlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
