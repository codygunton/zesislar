Require Import isla.riscv64.riscv64.
From lithium Require Import proof_state pure_definitions.
From iris.bi Require Import interface.

(* Inspect direct nodes under a bound probe. Pure propositions may depend on
   the probe. A spatial frame must remain independent of it. *)
Ltac zesu_entry_witness_applied_phase fuel witness node :=
  lazymatch fuel with
  | O => fail 0 "The witness body has too many local aliases."
  | S ?remaining =>
      let node := eval cbv beta iota zeta delta [LET_ID] in node in
      lazymatch node with
      | @bi_pure _ _ => idtac
      | @bi_sep _ ?first_body ?second_body =>
          zesu_entry_witness_applied_phase remaining witness first_body;
          zesu_entry_witness_applied_phase remaining witness second_body
      | _ =>
          first [
            lazymatch node with
            | ?local_head ?argument =>
                is_var local_head;
                let expanded := eval cbv beta iota zeta delta [local_head LET_ID] in node in
                assert_fails (constr_eq expanded node);
                zesu_entry_witness_applied_phase remaining witness expanded
            end
          | tryif lazymatch node with context [witness] => idtac end
            then fail 0 "The spatial frame depends on the witness."
            else idtac]
      end
  end.

(* The temporary probe belongs only to this checked function term. The guard
   does not introduce a witness into the caller's proof state. *)
Ltac zesu_entry_witness_body_phase fuel body :=
  assert_fails (has_evar body);
  let body_type := type of body in
  assert_fails (has_evar body_type);
  lazymatch body_type with
  | ?domain -> _ =>
      let probe := fresh "witnessPhaseProbe" in
      let checked := constr:((fun probe : domain => ltac:(
        let applied := constr:(body probe) in
        zesu_entry_witness_applied_phase fuel constr:(probe) applied;
        exact I)) : domain -> True) in
      idtac
  end.

Ltac zesu_entry_witness_body_ready body :=
  zesu_entry_witness_body_phase constr:(128%nat) body.
