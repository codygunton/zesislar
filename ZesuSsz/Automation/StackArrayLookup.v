(* C2: the word a block loads lives inside an array the block holds.

   Islaris already reads through an array. `li_wp_read_mem` has an
   `MKArray` branch, and `tac_mem_mapsto_array_eq` picks the array out of
   the context when the address is inside it. What Islaris cannot do is
   prove that the address is inside it, because the two facts that decide
   that -- the frame pointer does not wrap, and the array is as long as
   the witness says -- are folded inside one hypothesis, and the hint's
   solver is `bv_solve`, which reads hypotheses and cannot unfold a name.

   So this is the same hint with a stronger solver, at a higher priority.
   `zesu_witness_arith` (`PureFacts.v`) unfolds what the witness says,
   adds what a registered lemma derives from it, normalizes the lengths,
   and hands the result to `lia` or `bv_solve`.

   The guard is the shape a stack frame makes: an array based at
   `bv_unsigned X + m`, an address `bv_unsigned (X + k)` with the same X,
   and literal m and k. Every other array in the context fails the guard
   in one match and costs nothing, which matters: the post-withdrawals
   frame holds about twenty arrays by the time the seal chain is open.

   What it does not do: it never splits the array. The word comes out
   through Islaris's own `MKArray` branch, which hands the array back
   whole, so the next boundary still sees one array and not three
   pieces. That is why this rule is a hint on the selection and not a
   `Subsume`. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Ltac zesu_literal_Z value :=
  let reduced := eval vm_compute in value in
  lazymatch reduced with
  | Z0 => idtac
  | Zpos _ => idtac
  | Zneg _ => idtac
  end.

Ltac zesu_stack_array_range :=
  lazymatch goal with
  | |- (bv_unsigned ?base + ?offset <= bv_unsigned (?base' + ?delta) < _) \/ _ =>
      constr_eq base base';
      zesu_literal_Z offset;
      zesu_literal_Z (bv_unsigned delta)
  end;
  left; split; zesu_witness_arith.

#[global] Hint Extern 9 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ∗ _)
    (mem_mapsto_kind_prop _ _) _) =>
  (apply tac_mem_mapsto_array_eq; zesu_stack_array_range)
  : typeclass_instances.
