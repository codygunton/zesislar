(* The boundary terms of the entriesToOwnedSlice block composition.
   EntriesToOwnedSliceBlockObligations.v (generated) and
   EntriesToOwnedSliceGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Local Open Scope Z_scope.

(* The contract continuation of EntriesToOwnedSliceContractCorrect at
   returnAddress. Every table entry carries it as K; a block that reaches the
   return consumes it through the return package's end bridge. *)
Definition entriesToOwnedSliceContinuation `{!islaG Sigma} `{!threadG}
    (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress (∃ outcome : ToOwnedSliceOutcome,
    ⌜bv_unsigned (toOwnedReturnAddress (entriesBase args)) = returnAddress /\
      toOwnedSliceDomain entriesElementBytes (entriesBase args) /\
      toOwnedSliceAllows entriesElementBytes entriesEmptyPointer (entriesBase args) outcome⌝ ∗
    toOwnedSliceExit entriesElementBytes entriesLog2Alignment (entriesBase args) outcome).
Global Instance : LithiumUnfold (@entriesToOwnedSliceContinuation) := I.
Global Typeclasses Opaque entriesToOwnedSliceContinuation.

(* The table code: the own code and the four callee specs at their entries
   (the allocator's alloc, remap and free, and memcpy). *)
Definition entriesToOwnedSliceTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (entriesToOwnedSliceSelectedCode ∗
   □ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec ∗
   □ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec ∗
   □ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Global Instance : LithiumUnfold (@entriesToOwnedSliceTableCode) := I.
Global Typeclasses Opaque entriesToOwnedSliceTableCode.

(* A block statement tagged with its block address and its entry constant;
   the composition selects the statement of a table slot by both tags. *)
Definition entriesToOwnedSliceBlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
