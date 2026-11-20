(* The boundary terms of the nextUint64 block composition.
   NextUint64BlockObligations.v (generated) and
   NextUint64GeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.
Local Open Scope Z_scope.

(* Every table entry carries it as K: the generated return entry at
   returnAddress. The return join 0x0070 consumes it; the end bridge of the
   composition turns the return entry into the contract exit. *)
Definition nextUint64Continuation `{!islaG Sigma} `{!threadG}
    (args : NextUint64Args) (returnAddress : Z) : iProp Sigma :=
  instr_pre returnAddress
    (ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.fp_machineReturn
      args returnAddress emp).
Global Instance : LithiumUnfold (@nextUint64Continuation) := I.
Global Typeclasses Opaque nextUint64Continuation.

(* The table code: the own code and decodeItem's call spec at its entry. *)
Definition nextUint64TableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (nextUint64SelectedCode ∗ □ instr_pre decodeItemEntry decodeItemCallSpec2)%I.
Global Instance : LithiumUnfold (@nextUint64TableCode) := I.
Global Typeclasses Opaque nextUint64TableCode.

(* A block statement tagged with its block address and its entry constant;
   the composition selects the statement of a table slot by both tags. *)
Definition nextUint64BlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
