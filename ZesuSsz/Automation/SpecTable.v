(* C4: find a specification in the spec table.

   `InstrSpecs/Lookup.v` defines
   `find_in_context_instr_body_lookup_resources_inst` and never registers
   it, so `spec_instr_resources` -- which every segment carries -- is dead
   weight: the search finds the raw instruction at an address but never
   its specification. Three of the seven write-success segments stop on
   that, asking `∃ : isla_trace` where the table holds the answer. It is
   the class that blocks the most segments.

   Registering the instance as Islaris writes it does fire, and the
   epilogue's frame falls from 101 to 23, but its
   `⌜lookup address = Some body⌝` premise is left as a goal: when `body`
   is already constrained from elsewhere the equation is false and the
   search stalls on it, as `body_lookup 87876 = Some (mmio_range …)`.

   So the lookup moves into typeclass resolution, where it either
   computes the entry or fails at once and the search falls through to
   the raw instruction exactly as before.

   NOT exported from `Automation/All.v`: a `find_in_context` instance
   changes the search for every proof in the repository, and this one has
   only been measured on the segments. A module opts in by importing it,
   which is what a generated module does. *)

Require Import ZesuSsz.Automation.Finish.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Section spec_table.
  Context `{!islaG Sigma} `{!threadG}.

  Class ZesuSpecAt (address : Z) (body : iProp Sigma) : Prop :=
    zesu_spec_at : Index.body_lookup address = Some body.

  Lemma find_in_context_zesu_spec_table address body
      `{!ZesuSpecAt address body} later continuation :
    (Index.spec_instr_resources ∗ continuation (IKPre false body))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    rewrite /Index.spec_instr_resources.
    exact (find_in_context_instr_body_lookup_resources_at
             address Index.body_lookup body zesu_spec_at later continuation).
  Qed.

  Definition find_in_context_zesu_spec_table_inst address :=
    [instance find_in_context_zesu_spec_table address with FICSyntactic].
  (* Ahead of the raw-instruction instance, which Islaris registers at 11:
     an address that has a specification should be entered through it. *)
  Global Existing Instance find_in_context_zesu_spec_table_inst | 10.

End spec_table.

Global Hint Extern 1 (ZesuSpecAt _ _) =>
  (unfold ZesuSpecAt; reflexivity) : typeclass_instances.
