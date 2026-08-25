(** Reusable instruction specifications.

    Each spec describes what one instruction does in terms of separation-logic
    resources — no Isla trace in sight. Mark each with [LithiumUnfold] so the
    proof search can look inside it. The dump invokes them via [//@spec:] and
    [//@import:] annotations.

    Start with the most common instructions and grow the library as you
    encounter new opcodes in the binary. *)
Require Import isla.isla.
Require Import isla.riscv64.riscv64.

(* TODO: add specs here. Copy mv_spec from islaris-tutorial/InstrSpecs/Specs.v
   as a starting point. The pattern:

   Definition mv_spec `{!islaG Σ} `{!threadG}
       (pc : Z) (Rdst Rsrc : string) : iProp Σ :=
     <precondition> -∗ instr_pre (pc + 4) <postcondition>.

   Global Instance : LithiumUnfold (@mv_spec) := I.
*)
