(* The two inclusions a returning call needs, and nothing else.

   These live below the hooks so that `Hooks.v` can use them: the project's
   Lithium hook redefinitions all belong in that one module, and a tactic
   there cannot depend on a module that imports it. *)

Require Import isla.riscv64.riscv64.

Section trace_tail.

  (* `scons_snap` only adds a constraint on the snapshot that `scons` does
     not make, so once the open spec is the caller's tail the inclusion
     holds outright. `spec_solver` is Islaris's own solver for these
     (theories/spec.v); the hand line spells it out as
     `unfold subseteq, spec_subseteq, scons, scons_snap; naive_solver`. *)
  Lemma zesu_scons_snap_subseteq_scons (event : seq_event)
      (accept : seq_snapshot -> Prop) (tail : spec) :
    scons_snap event accept tail ⊆ scons event tail.
  Proof. spec_solver. Qed.

  Lemma zesu_scons_subseteq_scons (event : seq_event) (tail : spec) :
    scons event tail ⊆ scons event tail.
  Proof. spec_solver. Qed.

End trace_tail.
