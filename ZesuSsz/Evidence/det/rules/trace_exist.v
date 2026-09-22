(* Candidate rule: supply the trace witness when the existential is opened,
   not after.

   Splitting `∃ x : spec *ₗ (), body x` into evars and letting Lithium
   continue does not work: with the spec open, `instr_pre … ?x` matches
   anything in the context and the search does not come back. A probe with
   that rule ran 171 s and was killed at the 6 GiB job cap.

   The hand proof does not open an evar either. It writes the witness
   first, and the witness is always the caller's tail -- the second
   argument of the `scons` the inclusion has on its right. That term does
   not mention the bound variable, so it can be read out from under the
   binder and supplied directly. *)

(* Once the witness is the caller's tail the inclusion holds outright:
   `scons_snap` only adds a constraint on the snapshot that `scons` does
   not make. Discharging it here keeps the pair together, so the search
   never sees a half-instantiated spec. *)
Ltac zesu_close_trace_inclusion :=
  iPureIntro; exact (zesu_scons_snap_subseteq_scons _ _ _).

Ltac zesu_open_trace_exist :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      match goal with
      | |- context [scons _ ?tail] =>
          iExists (tail, tt)ₗ;
          try (iSplit; [zesu_close_trace_inclusion |])
      end
  end.

(* Not kept: registering `find_in_context_instr_body_lookup_resources_inst`
   from `InstrSpecs/Lookup.v`, which Islaris defines and never registers,
   so `spec_instr_resources` is dead weight for the search. At priority 10
   it does fire and the frame falls from 47 to 8, but it then tries to
   discharge the lemma's own `instr_body ENTRY P` from the table and
   unifies the specification with the wrong entry
   (`body_lookup 87876 = Some (mmio_range …)`). The instance needs a guard
   that excludes the goal's own entry address before it can be registered.
   Recorded here as a WP6 ticket, not a rule. *)
