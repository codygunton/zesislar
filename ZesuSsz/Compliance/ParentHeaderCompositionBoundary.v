(* The two boundary terms of the decodeParentHeader block composition.
   ParentHeaderBlockObligations.v (generated) and
   ParentHeaderGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Contracts.NextUint64CallSpec2.
Local Open Scope Z_scope.

(* The contract continuation of ParentHeaderContractCorrect at returnAddress.
   Every table entry carries it as K; a block that reaches the return or the
   memcpy tail consumes it. *)
Definition parentHeaderContinuation `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress (∃ outcome : ParentHeaderOutcome,
    ⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\
      parentHeaderAllows (parentHeaderCall args) outcome⌝ ∗
    parentHeaderExitResources args outcome).
Global Instance : LithiumUnfold (@parentHeaderContinuation) := I.
Global Typeclasses Opaque parentHeaderContinuation.

(* The table code: the own code and the three callee specs at their entries.
   The composition derives it from the contract code, nextUint64's contract
   and decodeItem's compliance. *)
Definition parentHeaderTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (parentHeaderSelectedCode ∗
   □ instr_pre decodeItemEntry decodeItemCallSpec2 ∗
   □ instr_pre nextUint64Entry nextUint64CallSpec2 ∗
   memcpyCallPremise)%I.
Global Instance : LithiumUnfold (@parentHeaderTableCode) := I.
Global Typeclasses Opaque parentHeaderTableCode.

(* A block statement tagged with its block address. The composition selects
   the statement of a table slot by the tag; the tag unfolds to the statement. *)
Definition parentHeaderBlockAt (address : Z) (statement : Prop) : Prop := statement.
