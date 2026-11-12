Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Local Open Scope Z_scope.

(* The callee stack pointer of nextUint64's decodeItem call, sp - 96, must be
   16-byte aligned. The alignment of sp exists only inside the folded domain;
   its registered derivation is the only route to the solvers. *)
Check nextUint64BoundaryDomainStackAlignmentDerivedFacts.

Lemma nextuint64_callee_stack_alignment `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (R : iProp Sigma) :
  nextUint64BoundaryDomain params ->
  R -∗ (⌜bv_unsigned (Z_to_bv 64 (nextStackPointer (nextUint64Base params)) +
           BV 64 18446744073709551520)%bv mod 16 = 0⌝ ∗ R).
Proof. intros Hdomain. iIntros "HR". zesu_block2. Qed.
